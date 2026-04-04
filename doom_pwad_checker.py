#!/usr/bin/env python3
"""Validate Doom WAD/PWAD structure and run classic-map geometry checks."""

from __future__ import annotations

import argparse
import re
import struct
from dataclasses import dataclass, field
from pathlib import Path

WAD_HEADER = struct.Struct("<4sii")
WAD_DIRECTORY_ENTRY = struct.Struct("<ii8s")
ENTRY_SIZE = WAD_DIRECTORY_ENTRY.size

VERTEX_STRUCT = struct.Struct("<hh")
LINEDEF_STRUCT = struct.Struct("<hhhhhhh")
SIDEDEF_STRUCT = struct.Struct("<hh8s8s8sh")
SECTOR_STRUCT = struct.Struct("<hh8s8shhh")
THING_STRUCT = struct.Struct("<hhhhh")

MAP_MARKER_RE = re.compile(r"^(MAP\d\d|E\dM\d)$")
CLASSIC_MAP_LUMPS = (
    "THINGS",
    "LINEDEFS",
    "SIDEDEFS",
    "VERTEXES",
    "SEGS",
    "SSECTORS",
    "NODES",
    "SECTORS",
    "REJECT",
    "BLOCKMAP",
)
SKY_FLAT_NAMES = {"F_SKY1"}

POLYOBJ_STARTLINE = "Polyobj_StartLine"
POLYOBJ_EXPLICITLINE = "Polyobj_ExplicitLine"
POLYOBJ_ACTION_BY_SPECIAL: dict[int, str] = {
    1: POLYOBJ_STARTLINE,
    2: "Polyobj_RotateLeft",
    3: "Polyobj_RotateRight",
    4: "Polyobj_Move",
    5: POLYOBJ_EXPLICITLINE,
    6: "Polyobj_MoveTimes8",
    7: "Polyobj_DoorSwing",
    8: "Polyobj_DoorSlide",
    59: "Polyobj_OR_MoveToSpot",
    86: "Polyobj_MoveToSpot",
    87: "Polyobj_Stop",
    88: "Polyobj_MoveTo",
    89: "Polyobj_OR_MoveTo",
    90: "Polyobj_OR_RotateLeft",
    91: "Polyobj_OR_RotateRight",
    92: "Polyobj_OR_Move",
    93: "Polyobj_OR_MoveTimes8",
}
POLYOBJ_ANCHOR_TYPES = {9300}
POLYOBJ_STARTSPOT_TYPES = {9301, 9302, 9303}
UDMF_KNOWN_SECTOR_EFFECTS = {
    0,
    1,
    2,
    3,
    4,
    26,
    27,
    40,
    41,
    42,
    43,
    44,
    45,
    46,
    47,
    48,
    49,
    50,
    51,
    65,
    66,
    67,
    68,
    69,
    71,
    72,
    74,
    75,
    76,
    77,
    78,
    79,
    80,
    81,
    82,
    83,
    84,
    85,
    87,
    90,
    105,
    115,
    116,
    118,
    195,
    196,
    197,
    198,
    199,
    200,
    201,
    202,
    203,
    204,
    205,
    206,
    207,
    208,
    209,
    210,
    211,
    212,
    213,
    214,
    215,
    216,
    217,
    218,
    219,
    220,
    221,
    222,
    223,
    224,
} | set(range(225, 245))


@dataclass(frozen=True)
class LumpInfo:
    index: int
    name: str
    offset: int
    size: int

    @property
    def end(self) -> int:
        return self.offset + self.size


@dataclass
class Vertex:
    index: int
    x: int
    y: int
    linedefs: list[int] = field(default_factory=list)


@dataclass
class Linedef:
    index: int
    start: int
    end: int
    flags: int
    special: int
    tag: int
    front: int
    back: int
    args: tuple[int, int, int, int, int] = (0, 0, 0, 0, 0)


@dataclass
class Sidedef:
    index: int
    x_offset: int
    y_offset: int
    high_tex: str
    low_tex: str
    mid_tex: str
    sector: int
    line: int = -1
    is_front: bool = True


@dataclass
class Sector:
    index: int
    floor_height: int
    ceil_height: int
    floor_tex: str
    ceil_tex: str
    light: int
    special: int
    tag: int
    sidedefs: list[int] = field(default_factory=list)


@dataclass
class Thing:
    index: int
    type: int
    angle: int
    class_name: str = ""


@dataclass
class ClassicMapModel:
    map_name: str
    vertices: list[Vertex]
    linedefs: list[Linedef]
    sidedefs: list[Sidedef]
    sectors: list[Sector]
    things: list[Thing] = field(default_factory=list)
    is_udmf: bool = False


@dataclass(frozen=True)
class EffectiveLineState:
    front_side_entry: int | None
    back_side_entry: int | None
    front_sector: int | None
    back_sector: int | None


@dataclass(frozen=True)
class EffectiveSideEntry:
    line_index: int
    is_front: bool
    left_vertex: int
    right_vertex: int


def decode_lump_name(raw: bytes) -> str:
    return raw.rstrip(b"\x00").decode("ascii", errors="ignore").upper()


def decode_texture_name(raw: bytes) -> str:
    return raw.rstrip(b"\x00").decode("ascii", errors="ignore").upper()


def is_empty_texture(name: str) -> bool:
    return (not name) or name == "-"


def parse_wad(path: Path) -> tuple[str, int, int, int, list[LumpInfo]]:
    file_size = path.stat().st_size
    with path.open("rb") as handle:
        header = handle.read(WAD_HEADER.size)
        if len(header) != WAD_HEADER.size:
            raise ValueError("Short WAD header (expected 12 bytes)")
        ident_raw, lump_count, directory_offset = WAD_HEADER.unpack(header)

        try:
            ident = ident_raw.decode("ascii")
        except UnicodeDecodeError as exc:
            raise ValueError(f"Invalid WAD id bytes: {ident_raw!r}") from exc

        if ident not in {"IWAD", "PWAD"}:
            raise ValueError(f"Invalid WAD id: {ident!r} (expected IWAD or PWAD)")
        if lump_count < 0:
            raise ValueError(f"Negative lump count: {lump_count}")
        if directory_offset < 0:
            raise ValueError(f"Negative directory offset: {directory_offset}")

        expected_dir_bytes = lump_count * ENTRY_SIZE
        if directory_offset + expected_dir_bytes > file_size:
            raise ValueError(
                "Directory extends past end of file "
                f"(dir_off={directory_offset}, dir_bytes={expected_dir_bytes}, file_size={file_size})"
            )

        handle.seek(directory_offset)
        lumps: list[LumpInfo] = []
        for idx in range(lump_count):
            rec = handle.read(ENTRY_SIZE)
            if len(rec) != ENTRY_SIZE:
                raise ValueError(f"Short directory entry at index {idx}")
            offset, size, raw_name = WAD_DIRECTORY_ENTRY.unpack(rec)
            lumps.append(
                LumpInfo(
                    index=idx,
                    name=decode_lump_name(raw_name),
                    offset=offset,
                    size=size,
                )
            )

    return ident, lump_count, directory_offset, file_size, lumps


def read_lump_bytes(path: Path, lump: LumpInfo) -> bytes:
    with path.open("rb") as handle:
        handle.seek(lump.offset)
        return handle.read(lump.size)


def analyze_layout(
    file_size: int,
    directory_offset: int,
    lumps: list[LumpInfo],
) -> tuple[list[str], list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []
    infos: list[str] = []

    invalid_name_count = 0
    duplicates: dict[str, int] = {}
    segments: list[tuple[int, int, str]] = []
    zero_size_count = 0

    for lump in lumps:
        if lump.size == 0:
            zero_size_count += 1
        if lump.offset < 0:
            errors.append(f"lump[{lump.index}] {lump.name}: negative offset {lump.offset}")
            continue
        if lump.size < 0:
            errors.append(f"lump[{lump.index}] {lump.name}: negative size {lump.size}")
            continue

        if lump.end > file_size:
            errors.append(
                f"lump[{lump.index}] {lump.name}: data out of file bounds "
                f"(offset={lump.offset}, size={lump.size}, end={lump.end}, file_size={file_size})"
            )
        if lump.size > 0 and lump.offset >= directory_offset:
            warnings.append(
                f"lump[{lump.index}] {lump.name}: data starts inside/after directory area "
                f"(offset={lump.offset}, dir_off={directory_offset})"
            )

        if not lump.name or len(lump.name) > 8:
            invalid_name_count += 1

        duplicates[lump.name] = duplicates.get(lump.name, 0) + 1
        if lump.size > 0:
            segments.append((lump.offset, lump.end, f"lump[{lump.index}] {lump.name}"))

    segments.sort(key=lambda x: (x[0], x[1]))
    for prev, cur in zip(segments, segments[1:]):
        prev_start, prev_end, prev_label = prev
        cur_start, cur_end, cur_label = cur
        if cur_start < prev_end:
            errors.append(
                "overlap: "
                f"{prev_label} [{prev_start},{prev_end}) intersects "
                f"{cur_label} [{cur_start},{cur_end})"
            )
        elif cur_start > prev_end:
            infos.append(f"gap: bytes [{prev_end},{cur_start}) are not referenced by any lump")

    duplicate_count = sum(1 for c in duplicates.values() if c > 1)
    if duplicate_count:
        infos.append(f"{duplicate_count} duplicate lump name(s) detected")
    if invalid_name_count:
        warnings.append(f"{invalid_name_count} lump name(s) were empty/invalid after decode")
    infos.append(f"zero-size lumps: {zero_size_count}")

    return errors, warnings, infos


def map_sections(lumps: list[LumpInfo]) -> list[tuple[str, list[LumpInfo]]]:
    sections: list[tuple[str, list[LumpInfo]]] = []
    current_name: str | None = None
    current_lumps: list[LumpInfo] = []

    for lump in lumps:
        if MAP_MARKER_RE.match(lump.name):
            if current_name is not None:
                sections.append((current_name, current_lumps))
            current_name = lump.name
            current_lumps = []
            continue
        if current_name is not None:
            current_lumps.append(lump)

    if current_name is not None:
        sections.append((current_name, current_lumps))

    return sections


def require_lump(map_name: str, map_lumps: list[LumpInfo], lump_name: str) -> LumpInfo:
    for lump in map_lumps:
        if lump.name == lump_name:
            return lump
    raise ValueError(f"{map_name}: missing required lump {lump_name}")


def unpack_entries(
    blob: bytes,
    struct_obj: struct.Struct,
    label: str,
    map_name: str,
) -> list[tuple[int, ...]]:
    if len(blob) % struct_obj.size != 0:
        raise ValueError(
            f"{map_name}: {label} size {len(blob)} is not a multiple of {struct_obj.size}"
        )
    out: list[tuple[int, ...]] = []
    for off in range(0, len(blob), struct_obj.size):
        out.append(struct_obj.unpack_from(blob, off))
    return out


def parse_classic_map(path: Path, map_name: str, map_lumps: list[LumpInfo]) -> ClassicMapModel:
    things_blob = read_lump_bytes(path, require_lump(map_name, map_lumps, "THINGS"))
    vertex_blob = read_lump_bytes(path, require_lump(map_name, map_lumps, "VERTEXES"))
    linedef_blob = read_lump_bytes(path, require_lump(map_name, map_lumps, "LINEDEFS"))
    sidedef_blob = read_lump_bytes(path, require_lump(map_name, map_lumps, "SIDEDEFS"))
    sector_blob = read_lump_bytes(path, require_lump(map_name, map_lumps, "SECTORS"))

    things_raw = unpack_entries(things_blob, THING_STRUCT, "THINGS", map_name)
    vertices_raw = unpack_entries(vertex_blob, VERTEX_STRUCT, "VERTEXES", map_name)
    linedefs_raw = unpack_entries(linedef_blob, LINEDEF_STRUCT, "LINEDEFS", map_name)
    sidedefs_raw = unpack_entries(sidedef_blob, SIDEDEF_STRUCT, "SIDEDEFS", map_name)
    sectors_raw = unpack_entries(sector_blob, SECTOR_STRUCT, "SECTORS", map_name)

    things = [
        Thing(
            index=i,
            type=int(thing_type),
            angle=int(angle),
            class_name="",
        )
        for i, (_x, _y, angle, thing_type, _flags) in enumerate(things_raw)
    ]
    vertices = [Vertex(index=i, x=int(x), y=int(y)) for i, (x, y) in enumerate(vertices_raw)]
    linedefs = [
        Linedef(
            index=i,
            start=int(v1),
            end=int(v2),
            flags=int(flags),
            special=int(special),
            tag=int(tag),
            front=int(front),
            back=int(back),
        )
        for i, (v1, v2, flags, special, tag, front, back) in enumerate(linedefs_raw)
    ]
    sidedefs = [
        Sidedef(
            index=i,
            x_offset=int(xoff),
            y_offset=int(yoff),
            high_tex=decode_texture_name(high),
            low_tex=decode_texture_name(low),
            mid_tex=decode_texture_name(mid),
            sector=int(sector_idx),
        )
        for i, (xoff, yoff, high, low, mid, sector_idx) in enumerate(sidedefs_raw)
    ]
    sectors = [
        Sector(
            index=i,
            floor_height=int(floor_h),
            ceil_height=int(ceil_h),
            floor_tex=decode_texture_name(floor_tex),
            ceil_tex=decode_texture_name(ceil_tex),
            light=int(light),
            special=int(special),
            tag=int(tag),
        )
        for i, (floor_h, ceil_h, floor_tex, ceil_tex, light, special, tag) in enumerate(sectors_raw)
    ]

    for line in linedefs:
        if 0 <= line.start < len(vertices):
            vertices[line.start].linedefs.append(line.index)
        if 0 <= line.end < len(vertices):
            vertices[line.end].linedefs.append(line.index)

        for side_index, is_front in ((line.front, True), (line.back, False)):
            if 0 <= side_index < len(sidedefs):
                sd = sidedefs[side_index]
                sd.line = line.index
                sd.is_front = is_front

    for side in sidedefs:
        if 0 <= side.sector < len(sectors):
            sectors[side.sector].sidedefs.append(side.index)

    return ClassicMapModel(
        map_name=map_name,
        vertices=vertices,
        linedefs=linedefs,
        sidedefs=sidedefs,
        sectors=sectors,
        things=things,
        is_udmf=False,
    )


UDMF_BLOCK_RE = re.compile(r"(?ms)\b(vertex|linedef|sidedef|sector|thing)\s*\{(.*?)\}")
UDMF_PROP_RE = re.compile(r"(?mi)^\s*([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(\"(?:[^\"\\\\]|\\\\.)*\"|[^;]+)\s*;\s*$")
MAPINFO_MAP_BLOCK_RE = re.compile(r"(?ims)^\s*map\s+([A-Za-z0-9_]+)\b[^\{]*\{(.*?)^\s*\}")


def _udmf_unquote(value: str) -> str:
    value = value.strip()
    if len(value) >= 2 and value[0] == '"' and value[-1] == '"':
        return bytes(value[1:-1], "utf-8").decode("unicode_escape")
    return value


def _udmf_int(props: dict[str, str], name: str, default: int = 0) -> int:
    raw = props.get(name)
    if raw is None:
        return default
    raw = raw.strip()
    if not raw:
        return default
    try:
        return int(raw, 10)
    except ValueError:
        try:
            return int(float(raw))
        except ValueError:
            return default


def _udmf_float(props: dict[str, str], name: str, default: float = 0.0) -> float:
    raw = props.get(name)
    if raw is None:
        return default
    raw = raw.strip()
    if not raw:
        return default
    try:
        return float(raw)
    except ValueError:
        return default


def parse_udmf_map(path: Path, map_name: str, map_lumps: list[LumpInfo]) -> ClassicMapModel:
    by_name = {l.name: l for l in map_lumps}
    textmap_lump = by_name.get("TEXTMAP")
    if textmap_lump is None:
        raise ValueError("TEXTMAP lump is missing")
    text = read_lump_bytes(path, textmap_lump).decode("utf-8", errors="ignore")

    vertices: list[Vertex] = []
    linedefs: list[Linedef] = []
    sidedefs: list[Sidedef] = []
    sectors: list[Sector] = []
    things: list[Thing] = []

    for block_match in UDMF_BLOCK_RE.finditer(text):
        block_type = block_match.group(1).lower()
        body = block_match.group(2)
        props: dict[str, str] = {}
        for prop_match in UDMF_PROP_RE.finditer(body):
            key = prop_match.group(1).strip().lower()
            value = prop_match.group(2).strip()
            props[key] = _udmf_unquote(value)

        if block_type == "vertex":
            vx = int(round(_udmf_float(props, "x", 0.0)))
            vy = int(round(_udmf_float(props, "y", 0.0)))
            vertices.append(Vertex(index=len(vertices), x=vx, y=vy))
            continue

        if block_type == "linedef":
            linedefs.append(
                Linedef(
                    index=len(linedefs),
                    start=_udmf_int(props, "v1", -1),
                    end=_udmf_int(props, "v2", -1),
                    flags=_udmf_int(props, "flags", 0),
                    special=_udmf_int(props, "special", 0),
                    tag=_udmf_int(props, "id", 0),
                    front=_udmf_int(props, "sidefront", -1),
                    back=_udmf_int(props, "sideback", -1),
                    args=(
                        _udmf_int(props, "arg0", 0),
                        _udmf_int(props, "arg1", 0),
                        _udmf_int(props, "arg2", 0),
                        _udmf_int(props, "arg3", 0),
                        _udmf_int(props, "arg4", 0),
                    ),
                )
            )
            continue

        if block_type == "sidedef":
            sidedefs.append(
                Sidedef(
                    index=len(sidedefs),
                    x_offset=_udmf_int(props, "offsetx", 0),
                    y_offset=_udmf_int(props, "offsety", 0),
                    high_tex=decode_texture_name(_udmf_unquote(props.get("texturetop", "-")).encode("ascii", errors="ignore")),
                    low_tex=decode_texture_name(_udmf_unquote(props.get("texturebottom", "-")).encode("ascii", errors="ignore")),
                    mid_tex=decode_texture_name(_udmf_unquote(props.get("texturemiddle", "-")).encode("ascii", errors="ignore")),
                    sector=_udmf_int(props, "sector", -1),
                )
            )
            continue

        if block_type == "sector":
            sectors.append(
                Sector(
                    index=len(sectors),
                    floor_height=_udmf_int(props, "heightfloor", 0),
                    ceil_height=_udmf_int(props, "heightceiling", 128),
                    floor_tex=decode_texture_name(_udmf_unquote(props.get("texturefloor", "FLOOR0_1")).encode("ascii", errors="ignore")),
                    ceil_tex=decode_texture_name(_udmf_unquote(props.get("textureceiling", "CEIL1_1")).encode("ascii", errors="ignore")),
                    light=_udmf_int(props, "lightlevel", 160),
                    special=_udmf_int(props, "special", 0),
                    tag=_udmf_int(props, "id", 0),
                )
            )
            continue

        if block_type == "thing":
            things.append(
                Thing(
                    index=len(things),
                    type=_udmf_int(props, "type", 0),
                    angle=_udmf_int(props, "angle", 0),
                    class_name=_udmf_unquote(props.get("class", "")),
                )
            )
            continue

    if not vertices:
        raise ValueError("No vertex blocks parsed from TEXTMAP")
    if not linedefs:
        raise ValueError("No linedef blocks parsed from TEXTMAP")
    if not sidedefs:
        raise ValueError("No sidedef blocks parsed from TEXTMAP")
    if not sectors:
        raise ValueError("No sector blocks parsed from TEXTMAP")

    for line in linedefs:
        if 0 <= line.start < len(vertices):
            vertices[line.start].linedefs.append(line.index)
        if 0 <= line.end < len(vertices):
            vertices[line.end].linedefs.append(line.index)

        for side_index, is_front in ((line.front, True), (line.back, False)):
            if 0 <= side_index < len(sidedefs):
                sd = sidedefs[side_index]
                sd.line = line.index
                sd.is_front = is_front

    for side in sidedefs:
        if 0 <= side.sector < len(sectors):
            sectors[side.sector].sidedefs.append(side.index)

    return ClassicMapModel(
        map_name=map_name,
        vertices=vertices,
        linedefs=linedefs,
        sidedefs=sidedefs,
        sectors=sectors,
        things=things,
        is_udmf=True,
    )


def parse_mapinfo_blocks(path: Path, lumps: list[LumpInfo]) -> dict[str, str]:
    mapinfo_lump = next((l for l in lumps if l.name == "MAPINFO"), None)
    if mapinfo_lump is None:
        return {}
    text = read_lump_bytes(path, mapinfo_lump).decode("utf-8", errors="ignore")
    out: dict[str, str] = {}
    for match in MAPINFO_MAP_BLOCK_RE.finditer(text):
        map_name = match.group(1).upper()
        body = match.group(2)
        if map_name not in out:
            out[map_name] = body
    return out


def line_sidedef_sector(model: ClassicMapModel, side_idx: int) -> int | None:
    if side_idx < 0 or side_idx >= len(model.sidedefs):
        return None
    sector_idx = model.sidedefs[side_idx].sector
    if sector_idx < 0 or sector_idx >= len(model.sectors):
        return None
    return sector_idx


def all_four_sides_same_sector(model: ClassicMapModel, line_a: Linedef, line_b: Linedef) -> bool:
    sectors = [
        line_sidedef_sector(model, line_a.front),
        line_sidedef_sector(model, line_a.back),
        line_sidedef_sector(model, line_b.front),
        line_sidedef_sector(model, line_b.back),
    ]
    same_sector = next((s for s in sectors if s is not None), None)
    if same_sector is None:
        return False
    return all(s == same_sector for s in sectors)


def is_identical_segment(model: ClassicMapModel, line_a: Linedef, line_b: Linedef) -> bool:
    if line_a.start < 0 or line_a.end < 0 or line_b.start < 0 or line_b.end < 0:
        return False
    if line_a.start >= len(model.vertices) or line_a.end >= len(model.vertices):
        return False
    if line_b.start >= len(model.vertices) or line_b.end >= len(model.vertices):
        return False
    a1 = model.vertices[line_a.start]
    a2 = model.vertices[line_a.end]
    b1 = model.vertices[line_b.start]
    b2 = model.vertices[line_b.end]
    return (a1.x == b1.x and a1.y == b1.y and a2.x == b2.x and a2.y == b2.y) or (
        a1.x == b2.x and a1.y == b2.y and a2.x == b1.x and a2.y == b1.y
    )


def intersects_interior(model: ClassicMapModel, line_a: Linedef, line_b: Linedef) -> bool:
    if (
        line_a.start < 0
        or line_a.end < 0
        or line_b.start < 0
        or line_b.end < 0
        or line_a.start >= len(model.vertices)
        or line_a.end >= len(model.vertices)
        or line_b.start >= len(model.vertices)
        or line_b.end >= len(model.vertices)
    ):
        return False

    a1 = model.vertices[line_a.start]
    a2 = model.vertices[line_a.end]
    b1 = model.vertices[line_b.start]
    b2 = model.vertices[line_b.end]

    x1, y1 = float(a1.x), float(a1.y)
    x2, y2 = float(a2.x), float(a2.y)
    x3, y3 = float(b1.x), float(b1.y)
    x4, y4 = float(b2.x), float(b2.y)

    div = (y4 - y3) * (x2 - x1) - (x4 - x3) * (y2 - y1)
    if div == 0.0:
        return False

    u_line = ((x4 - x3) * (y1 - y3) - (y4 - y3) * (x1 - x3)) / div
    u_ray = ((x2 - x1) * (y1 - y3) - (y2 - y1) * (x1 - x3)) / div
    return (0.0 < u_line < 1.0) and (0.0 < u_ray < 1.0)


def check_overlapping_lines(model: ClassicMapModel) -> list[str]:
    findings: list[str] = []
    lines = model.linedefs
    for i in range(len(lines)):
        line_a = lines[i]
        for j in range(i + 1, len(lines)):
            line_b = lines[j]

            if is_identical_segment(model, line_a, line_b):
                findings.append(
                    f"Linedefs {line_a.index} and {line_b.index} are overlapping and reference different sectors"
                )
                continue

            if intersects_interior(model, line_a, line_b) and not all_four_sides_same_sector(
                model, line_a, line_b
            ):
                findings.append(
                    f"Linedefs {line_a.index} and {line_b.index} are overlapping and reference different sectors"
                )
    return findings


def line_references_sector(model: ClassicMapModel, line: Linedef, sector_index: int) -> bool:
    front_sec = line_sidedef_sector(model, line.front)
    back_sec = line_sidedef_sector(model, line.back)
    return front_sec == sector_index or back_sec == sector_index


def check_unclosed_sectors(model: ClassicMapModel) -> list[str]:
    findings: list[str] = []

    for sector in model.sectors:
        found_holes: list[int] = []
        vertex_marks: dict[int, int] = {}

        for side_idx in sector.sidedefs:
            if side_idx < 0 or side_idx >= len(model.sidedefs):
                continue
            side = model.sidedefs[side_idx]
            if side.line < 0 or side.line >= len(model.linedefs):
                continue
            line = model.linedefs[side.line]
            if (
                line.start < 0
                or line.end < 0
                or line.start >= len(model.vertices)
                or line.end >= len(model.vertices)
            ):
                continue

            vertex_marks.setdefault(line.start, 0)
            vertex_marks.setdefault(line.end, 0)

            if side.is_front:
                vertex_marks[line.start] |= 1
                vertex_marks[line.end] |= 2
            else:
                vertex_marks[line.end] |= 1
                vertex_marks[line.start] |= 2

        for vertex_idx, mark in list(vertex_marks.items()):
            if mark == 3:
                continue

            if vertex_idx not in found_holes:
                found_holes.append(vertex_idx)

            if vertex_idx < 0 or vertex_idx >= len(model.vertices):
                continue
            vertex = model.vertices[vertex_idx]
            for line_idx in vertex.linedefs:
                if line_idx < 0 or line_idx >= len(model.linedefs):
                    continue
                line = model.linedefs[line_idx]
                if line_references_sector(model, line, sector.index):
                    continue
                for other_vertex in (line.start, line.end):
                    if (
                        other_vertex in vertex_marks
                        and vertex_marks[other_vertex] == 3
                        and other_vertex not in found_holes
                    ):
                        found_holes.append(other_vertex)

        if found_holes:
            findings.append(f"Sector {sector.index} is not closed")

    return findings


def other_sidedef_index(model: ClassicMapModel, side: Sidedef) -> int:
    if side.line < 0 or side.line >= len(model.linedefs):
        return -1
    line = model.linedefs[side.line]
    return line.back if side.is_front else line.front


def sector_has_sky_ceiling(model: ClassicMapModel, sector_idx: int) -> bool:
    if sector_idx < 0 or sector_idx >= len(model.sectors):
        return False
    return model.sectors[sector_idx].ceil_tex in SKY_FLAT_NAMES


def sector_has_sky_floor(model: ClassicMapModel, sector_idx: int) -> bool:
    if sector_idx < 0 or sector_idx >= len(model.sectors):
        return False
    return model.sectors[sector_idx].floor_tex in SKY_FLAT_NAMES


def high_required(model: ClassicMapModel, side: Sidedef) -> bool:
    other_idx = other_sidedef_index(model, side)
    if other_idx < 0 or other_idx >= len(model.sidedefs):
        return False
    if side.sector < 0 or side.sector >= len(model.sectors):
        return False
    other = model.sidedefs[other_idx]
    if other.sector < 0 or other.sector >= len(model.sectors):
        return False
    this_sector = model.sectors[side.sector]
    other_sector = model.sectors[other.sector]
    if sector_has_sky_ceiling(model, other.sector):
        return False
    return other_sector.ceil_height < this_sector.ceil_height


def low_required(model: ClassicMapModel, side: Sidedef) -> bool:
    other_idx = other_sidedef_index(model, side)
    if other_idx < 0 or other_idx >= len(model.sidedefs):
        return False
    if side.sector < 0 or side.sector >= len(model.sectors):
        return False
    other = model.sidedefs[other_idx]
    if other.sector < 0 or other.sector >= len(model.sectors):
        return False
    this_sector = model.sectors[side.sector]
    other_sector = model.sectors[other.sector]
    if sector_has_sky_floor(model, other.sector):
        return False
    return other_sector.floor_height > this_sector.floor_height


def check_unused_textures(model: ClassicMapModel) -> list[str]:
    findings: list[str] = []
    for side in model.sidedefs:
        if not is_empty_texture(side.high_tex) and not high_required(model, side):
            findings.append(f'Sidedef {side.index} has unused upper texture "{side.high_tex}"')
        if not is_empty_texture(side.low_tex) and not low_required(model, side):
            findings.append(f'Sidedef {side.index} has unused lower texture "{side.low_tex}"')
    return findings


def check_removed_unused_sectors(model: ClassicMapModel) -> list[str]:
    findings: list[str] = []
    for sector in model.sectors:
        has_attached_side = False
        for side_idx in sector.sidedefs:
            if 0 <= side_idx < len(model.sidedefs) and model.sidedefs[side_idx].line >= 0:
                has_attached_side = True
                break
        if not has_attached_side:
            findings.append(f"Sector {sector.index} was unused and has been removed.")
    return findings


def check_mapinfo_sky1_missing(map_name: str, mapinfo_blocks: dict[str, str]) -> list[str]:
    body = mapinfo_blocks.get(map_name.upper())
    if body is None:
        return []
    if re.search(r"(?im)^\s*sky1\s*=", body):
        return []
    return ["Skybox creation failed: Sky1 property is missing from the MAPINFO map definition"]


def line_is_zero_length(model: ClassicMapModel, line: Linedef) -> bool:
    if line.start < 0 or line.end < 0:
        return False
    if line.start >= len(model.vertices) or line.end >= len(model.vertices):
        return False
    if line.start == line.end:
        return True
    a = model.vertices[line.start]
    b = model.vertices[line.end]
    return a.x == b.x and a.y == b.y


def resolve_effective_side_index(
    model: ClassicMapModel,
    side_index: int,
    udmf_side_ref_limit: int,
) -> int | None:
    if side_index < 0:
        return None
    if model.is_udmf and side_index >= udmf_side_ref_limit:
        return None
    if side_index >= len(model.sidedefs):
        return None
    return side_index


def build_effective_line_state(
    model: ClassicMapModel,
) -> tuple[list[int], dict[int, EffectiveLineState], list[EffectiveSideEntry]]:
    candidate_lines: list[Linedef] = []
    if model.is_udmf:
        for line in model.linedefs:
            if not line_is_zero_length(model, line):
                candidate_lines.append(line)
    else:
        candidate_lines = list(model.linedefs)

    udmf_side_ref_limit = len(model.sidedefs)
    if model.is_udmf:
        udmf_side_ref_limit = 0
        for line in candidate_lines:
            if line.front >= 0:
                udmf_side_ref_limit += 1
            if line.back >= 0:
                udmf_side_ref_limit += 1

    ordered_line_indices: list[int] = []
    line_state: dict[int, EffectiveLineState] = {}
    side_entries: list[EffectiveSideEntry] = []

    for line in candidate_lines:
        ordered_line_indices.append(line.index)
        front_idx = resolve_effective_side_index(model, line.front, udmf_side_ref_limit)
        back_idx = resolve_effective_side_index(model, line.back, udmf_side_ref_limit)

        front_entry: int | None = None
        if front_idx is not None:
            front_entry = len(side_entries)
            side_entries.append(
                EffectiveSideEntry(
                    line_index=line.index,
                    is_front=True,
                    left_vertex=line.start,
                    right_vertex=line.end,
                )
            )

        back_entry: int | None = None
        if back_idx is not None:
            back_entry = len(side_entries)
            side_entries.append(
                EffectiveSideEntry(
                    line_index=line.index,
                    is_front=False,
                    left_vertex=line.end,
                    right_vertex=line.start,
                )
            )

        front_sector: int | None = None
        if front_idx is not None:
            sector_idx = model.sidedefs[front_idx].sector
            if 0 <= sector_idx < len(model.sectors):
                front_sector = sector_idx

        back_sector: int | None = None
        if back_idx is not None:
            sector_idx = model.sidedefs[back_idx].sector
            if 0 <= sector_idx < len(model.sectors):
                back_sector = sector_idx

        line_state[line.index] = EffectiveLineState(
            front_side_entry=front_entry,
            back_side_entry=back_entry,
            front_sector=front_sector,
            back_sector=back_sector,
        )

    return ordered_line_indices, line_state, side_entries


def check_missing_front_side_or_sector(model: ClassicMapModel) -> list[str]:
    findings: list[str] = []
    missing_front_lines: list[int] = []
    ordered_line_indices, line_state, _ = build_effective_line_state(model)

    for line_index in ordered_line_indices:
        state = line_state[line_index]
        if state.front_side_entry is None:
            findings.append(f"Line {line_index} has no front sector")
            missing_front_lines.append(line_index)
            findings.append(f"Linedef {line_index} does not have a front side.")
            continue
        if state.front_sector is None:
            findings.append(f"Line {line_index} has no front sector")

    if missing_front_lines:
        summary = "The following lines do not have a front sidedef:\n " + "\n ".join(
            str(i) for i in missing_front_lines
        )
        findings.append(summary)

    return findings


def check_unconnected_right_edges(model: ClassicMapModel) -> list[str]:
    # Mimics the "right edge is unconnected" checks in GZDoom's LoopSidedefs.
    _, line_state, side_entries = build_effective_line_state(model)
    left_vertex_side_counts: dict[int, int] = {}
    for side in side_entries:
        if side.left_vertex < 0 or side.left_vertex >= len(model.vertices):
            continue
        left_vertex_side_counts[side.left_vertex] = left_vertex_side_counts.get(side.left_vertex, 0) + 1

    findings: list[str] = []
    seen_lines: set[int] = set()
    for side in side_entries:
        state = line_state.get(side.line_index)
        if state is None:
            continue

        front_sector = state.front_sector
        back_sector = state.back_sector

        if front_sector == back_sector:
            other_side_ok = (
                (state.back_side_entry is not None)
                if side.is_front
                else (state.front_side_entry is not None)
            )
            if not other_side_ok and side.line_index not in seen_lines:
                findings.append(f"Line {side.line_index}'s right edge is unconnected")
                seen_lines.add(side.line_index)
            continue

        if side.right_vertex < 0 or side.right_vertex >= len(model.vertices):
            continue
        if left_vertex_side_counts.get(side.right_vertex, 0) == 0 and side.line_index not in seen_lines:
            findings.append(f"Line {side.line_index}'s right edge is unconnected")
            seen_lines.add(side.line_index)

    return findings


def format_index_series(indices: list[int]) -> str:
    if not indices:
        return ""
    if len(indices) == 1:
        return str(indices[0])
    if len(indices) == 2:
        return f"{indices[0]} and {indices[1]}"
    return ", ".join(str(i) for i in indices[:-1]) + f" and {indices[-1]}"


def format_polyobject_linedef_result(line_indices: list[int]) -> str:
    ordered = sorted(set(line_indices))
    if len(ordered) == 1:
        return f"Incorrect Polyobject setup for linedef {ordered[0]}"
    return f"Incorrect Polyobject setup for linedefs {format_index_series(ordered)}"


def check_polyobject_setup(model: ClassicMapModel) -> list[str]:
    if not model.is_udmf:
        return []

    polyobj_lines: dict[str, dict[int, list[int]]] = {}
    for line in model.linedefs:
        action_name = POLYOBJ_ACTION_BY_SPECIAL.get(line.special)
        if action_name is None:
            continue
        po_number = line.args[0] if line.args else 0
        by_number = polyobj_lines.setdefault(action_name, {})
        by_number.setdefault(po_number, []).append(line.index)

    anchors: dict[int, list[int]] = {}
    startspots: dict[int, list[int]] = {}
    for thing in model.things:
        cls = thing.class_name.lower()
        if cls == "$polyanchor" or thing.type in POLYOBJ_ANCHOR_TYPES:
            anchors.setdefault(thing.angle, []).append(thing.index)
            continue
        if cls in {"$polyspawn", "$polyspawncrush", "$polyspawnhurt"} or thing.type in POLYOBJ_STARTSPOT_TYPES:
            startspots.setdefault(thing.angle, []).append(thing.index)
            continue

    findings: list[str] = []

    for by_number in polyobj_lines.values():
        for po_number, line_indices in by_number.items():
            if po_number not in startspots:
                findings.append(format_polyobject_linedef_result(line_indices))

    for po_number, line_indices in polyobj_lines.get(POLYOBJ_STARTLINE, {}).items():
        if len(line_indices) > 1:
            findings.append(format_polyobject_linedef_result(line_indices))
        for line_index in line_indices:
            line = model.linedefs[line_index]
            mirror = line.args[1]
            if mirror <= 0:
                continue
            if mirror not in startspots:
                findings.append(format_polyobject_linedef_result([line_index]))
            if mirror == po_number:
                findings.append(format_polyobject_linedef_result([line_index]))

    for po_number, line_indices in polyobj_lines.get(POLYOBJ_EXPLICITLINE, {}).items():
        for line_index in line_indices:
            line = model.linedefs[line_index]
            mirror = line.args[2]
            if mirror <= 0:
                continue
            if mirror not in startspots:
                findings.append(format_polyobject_linedef_result([line_index]))
            if mirror == po_number:
                findings.append(format_polyobject_linedef_result([line_index]))

    return findings


def check_unknown_sector_effects(model: ClassicMapModel) -> list[str]:
    if not model.is_udmf:
        return []
    findings: list[str] = []
    for sector in model.sectors:
        effect = sector.special
        if effect != 0 and effect not in UDMF_KNOWN_SECTOR_EFFECTS:
            findings.append(f"Sector {sector.index} uses unknown effect {effect}")
    return findings


def map_finding_text(map_name: str, finding: str, map_filter: str | None) -> str:
    if map_filter is not None:
        return finding
    return f"{map_name}: {finding}"


def analyze_maps(path: Path, lumps: list[LumpInfo], map_filter: str | None) -> tuple[list[str], list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []
    infos: list[str] = []

    sections = map_sections(lumps)
    if not sections:
        warnings.append("no map marker lumps found (MAPxx / ExMy)")
        return errors, warnings, infos

    wanted = map_filter.upper() if map_filter else None
    if wanted is not None:
        sections = [item for item in sections if item[0] == wanted]
        if not sections:
            errors.append(f"requested map {wanted} was not found")
            return errors, warnings, infos

    mapinfo_blocks = parse_mapinfo_blocks(path, lumps)
    infos.append(f"maps detected: {len(sections)}")
    for map_name, map_lumps in sections:
        names = [l.name for l in map_lumps]

        has_textmap = "TEXTMAP" in names
        has_endmap = "ENDMAP" in names
        if has_textmap or has_endmap:
            if not (has_textmap and has_endmap):
                errors.append(
                    f"{map_name}: UDMF map is incomplete "
                    f"(TEXTMAP={'yes' if has_textmap else 'no'}, ENDMAP={'yes' if has_endmap else 'no'})"
                )
            else:
                if names.index("TEXTMAP") > names.index("ENDMAP"):
                    errors.append(f"{map_name}: ENDMAP appears before TEXTMAP")
                infos.append(f"{map_name}: UDMF map structure detected")
            if errors and errors[-1].startswith(f"{map_name}: ENDMAP appears before TEXTMAP"):
                continue
            try:
                model = parse_udmf_map(path, map_name, map_lumps)
            except Exception as exc:
                errors.append(f"{map_name}: failed parsing UDMF TEXTMAP: {exc}")
                continue

            polyobject_results = check_polyobject_setup(model)
            unknown_sector_results = check_unknown_sector_effects(model)
            removed_unused_sector_results = check_removed_unused_sectors(model)
            sky1_results = check_mapinfo_sky1_missing(map_name, mapinfo_blocks)
            missing_front_results = check_missing_front_side_or_sector(model)
            unconnected_right_results = check_unconnected_right_edges(model)
            overlap_results = check_overlapping_lines(model)
            unclosed_results = check_unclosed_sectors(model)
            unused_results = check_unused_textures(model)

            for text in polyobject_results:
                warnings.append(map_finding_text(map_name, text, wanted))
            for text in unknown_sector_results:
                warnings.append(map_finding_text(map_name, text, wanted))
            for text in removed_unused_sector_results:
                warnings.append(map_finding_text(map_name, text, wanted))
            for text in sky1_results:
                warnings.append(map_finding_text(map_name, text, wanted))
            for text in missing_front_results:
                warnings.append(map_finding_text(map_name, text, wanted))
            for text in unconnected_right_results:
                warnings.append(map_finding_text(map_name, text, wanted))
            for text in overlap_results:
                warnings.append(map_finding_text(map_name, text, wanted))
            for text in unclosed_results:
                warnings.append(map_finding_text(map_name, text, wanted))
            for text in unused_results:
                warnings.append(map_finding_text(map_name, text, wanted))
            continue

        missing = [name for name in CLASSIC_MAP_LUMPS if name not in names]
        if missing:
            errors.append(f"{map_name}: missing classic map lump(s): {', '.join(missing)}")
            continue

        infos.append(f"{map_name}: classic map lumps look complete")
        try:
            model = parse_classic_map(path, map_name, map_lumps)
        except Exception as exc:
            errors.append(f"{map_name}: failed parsing classic map data: {exc}")
            continue

        removed_unused_sector_results = check_removed_unused_sectors(model)
        sky1_results = check_mapinfo_sky1_missing(map_name, mapinfo_blocks)
        missing_front_results = check_missing_front_side_or_sector(model)
        unconnected_right_results = check_unconnected_right_edges(model)
        overlap_results = check_overlapping_lines(model)
        unclosed_results = check_unclosed_sectors(model)
        unused_results = check_unused_textures(model)

        for text in removed_unused_sector_results:
            warnings.append(map_finding_text(map_name, text, wanted))
        for text in sky1_results:
            warnings.append(map_finding_text(map_name, text, wanted))
        for text in missing_front_results:
            warnings.append(map_finding_text(map_name, text, wanted))
        for text in unconnected_right_results:
            warnings.append(map_finding_text(map_name, text, wanted))
        for text in overlap_results:
            warnings.append(map_finding_text(map_name, text, wanted))
        for text in unclosed_results:
            warnings.append(map_finding_text(map_name, text, wanted))
        for text in unused_results:
            warnings.append(map_finding_text(map_name, text, wanted))

    return errors, warnings, infos


def format_section(title: str, rows: list[str]) -> str:
    if not rows:
        return f"{title}: none"
    lines = [f"{title}: {len(rows)}"]
    lines.extend(f"  - {row}" for row in rows)
    return "\n".join(lines)


def run(path: Path, map_filter: str | None) -> int:
    try:
        ident, lump_count, directory_offset, file_size, lumps = parse_wad(path)
    except Exception as exc:
        print(f"ERROR: {path}: {exc}")
        return 2

    layout_errors, layout_warnings, layout_infos = analyze_layout(file_size, directory_offset, lumps)
    map_errors, map_warnings, map_infos = analyze_maps(path, lumps, map_filter)

    errors = layout_errors + map_errors
    warnings = layout_warnings + map_warnings
    infos = layout_infos + map_infos

    print(f"WAD: {path}")
    print(f"Type: {ident}")
    print(f"File size: {file_size} bytes")
    print(f"Lump count: {lump_count}")
    print(f"Directory offset: {directory_offset}")
    print(format_section("ERROR", errors))
    print(format_section("WARN", warnings))
    print(format_section("INFO", infos))

    if errors:
        return 1
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Check Doom WAD/PWAD structure and classic map consistency."
    )
    parser.add_argument("wad", type=Path, help="Path to WAD/PWAD file to validate")
    parser.add_argument(
        "--map",
        dest="map_filter",
        type=str,
        default=None,
        help="Optional map marker to check (example: MAP01).",
    )
    return parser


def main() -> None:
    parser = build_parser()
    args = parser.parse_args()
    raise SystemExit(run(args.wad.resolve(), args.map_filter))


if __name__ == "__main__":
    main()
