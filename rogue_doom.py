#!/usr/bin/env python3
"""Build a procedural 32-level Doom II PWAD from scratch.

Design goals:
- Small/Medium-sized maps.
- Corridor-heavy room-and-hall layouts.
- Fun without key hunting or wondering where to go.
- NetHack-style room feel, but with varied non-square room silhouettes.

Fingers crossed that noone use savegames (it is supposed to be roguelike after all

License: BSD-3   (https://opensource.org/license/bsd-3-clause)

(C) 2026-03-25   Bittervine
"""

from __future__ import annotations

import argparse
import csv
import math
import random
import shutil
import struct
import subprocess
import sys
import time
from datetime import datetime
from collections import deque
from dataclasses import dataclass, field
from enum import IntEnum
from pathlib import Path
from typing import Iterable, NamedTuple

try:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
except Exception:
    plt = None

ENABLE_PLOTS = False
DEBUG = 0
VERBOSE_TRACE_LOG = False
TRACE_LOG_FILENAME = "rogue_doom.log"
TRACE_MAP_START_TIME: float | None = None
TRACE_MAP_NAME: str = ""

WAD_HEADER = struct.Struct("<4sii")
WAD_DIRECTORY_ENTRY = struct.Struct("<ii8s")

EMPTY = 0
ROOM = 1
CORRIDOR = 2
TRANSITION = 3
DOOR = 4

TILE = 64
GRID_W = 96
GRID_H = 96
DOOR_NATIVE_WIDTH = 128
DOOR_WIDTH_CELLS = max(1, DOOR_NATIVE_WIDTH // TILE)
DOOR_THICKNESS = 8
START_ENTRY_DOOR_TEXTURE = "DOOR3"
START_ENTRY_DOOR_WIDTH_UNITS = 64
START_ENTRY_DOOR_HEIGHT_UNITS = 72
START_ENTRY_ALCOVE_DEPTH_UNITS = 4
CORRIDOR_END_FLAT_UNITS = 128
CORRIDOR_END_FLAT_CELLS = max(1, CORRIDOR_END_FLAT_UNITS // TILE)
ROOM_FLOOR_VARIATION_MAX = 128
ROOM_FLOOR_EDGE_DELTA_MAX = 96
ROOM_CEILING_CLEARANCE = 128
ROOM_GEOMETRY_SCALE = 1.0
INTERNAL_SECTOR_SCALE = 1.0
CORRIDOR_GEOMETRY_SCALE = 1.0
# Backward-compatible alias kept where corridor length code already uses this name.
CORRIDOR_LENGTH_SCALE = CORRIDOR_GEOMETRY_SCALE
CORRIDOR_LIGHT_FACTOR_MIN = 0.60
CORRIDOR_LIGHT_FACTOR_MAX = 1.00
ROOM_LIGHT_FACTOR_MIN = 0.75
ROOM_LIGHT_FACTOR_MAX = 1.00
CORRIDOR_STEP_RUN_UNITS = 2.0
CORRIDOR_STEP_HEIGHT_UNITS = 1
CORRIDOR_MAX_ABS_ELEVATION = 240
CORRIDOR_MAX_ADJ_STEP = 8
CONNECTED_ROOM_WALL_GAP_UNITS = 480.0
UNCONNECTED_ROOM_WALL_GAP_UNITS = 128.0
ROOM_CENTER_RELAXATION_PASSES = 28
SUNKEN_POOL_DAMAGE_SPECIAL = 5  # Damaging floor without light blink/flicker.
NON_COLORED_DOOR_REMOVAL_CHANCE = 0.25
ROOM_L_SHAPE_CHANCE = 0.50
CORRIDOR_VIAL_BOOST_MULTIPLIER = 1.50
CORRIDOR_ARMOR_BOOST_MULTIPLIER = 1.50
MONSTER_DEAF_CHANCE = 0.66
MONSTER_GAP_MARGIN_UNITS = 5.0
MONSTER_BOX_LINE_CLEARANCE_UNITS = 2.0
MAX_RETRIES = 16
DEFAULT_DEVELOPMENT_MAP_COUNT = 32
DEBUG_INTERNAL_SECTOR_PLACEMENT = True
DEBUG_DISABLE_PUDDLE_JAGGED = False
DEBUG_APPEND_DUMMY_LAST_LINE = False
DRAW_SIGNATURE = True
DEBUG_SAFE_MAP03 = False
ELEV_UNIT = 1
ROOM_SUNKEN_PLATFORM_DEPTH_UNITS = 6
OBJECT_MIN_SPACING_UNITS = 32.0
OBJECT_POOL_GRID_STEP_UNITS = OBJECT_MIN_SPACING_UNITS * 0.5
MIN_WALKABLE_GAP_WIDTH = 33.0  # 32 actually but +1 if my diet fails.
INTERNAL_SECTOR_WALL_CLEARANCE_UNITS = 48.0  # Extra margin to avoid diagonal pinch points.
OBJECT_MIN_HEADROOM_UNITS = 56
PLATFORM_EDGE_UNITS = 64.0
PLATFORM_CRATE_SIDE_TEXTURE = "CRATE1"
PLATFORM_CRATE_SIDE_TEXTURE_GRAY = "CRATE3"
PLATFORM_BLOCKING_SIDE_TEXTURE = "CRATINY"
PLATFORM_CRATE_TOP_FLAT = "CRATOP2"
PLATFORM_CRATE_TOP_FLAT_GRAY = "CRATOP1"
PLATFORM_BLOCKING_TOP_FLAT = "CRATOP1"
PLATFORM_GRAY_VARIANT_CHANCE = 0.50
INTERNAL_SECTOR_MAX_ROOM_COVERAGE = 0.25
INTERNAL_SECTOR_MAX_DIM_FRACTION = 0.75
PUDDLE_CORNER_CUT_RATIO = 0.25
PUDDLE_POSTPROCESS_PASSES = 3
PUDDLE_WAVE_AMPLITUDE_FACTOR = 0.68
PUDDLE_MIN_AREA_SCALE = 0.55
PUDDLE_MAX_AREA_SCALE = 1.65
PUDDLE_MIN_VERTEX_SPACING_UNITS = 5.0
PUDDLE_SECTOR_PROBABILITY = 0.10
KILLING_POOL_PROBABILITY = 0.34
KILLING_POOL_DEPTH_UNITS = 25  # Just above Doom's 24-unit step-up limit.
KILLING_POOL_FLOOR_TEXTURE = "DBRAIN1"
DOOR_LINTEL_STRIP_DEPTH_UNITS = 1.0
DOOR_LINTEL_CEILING_DROP_UNITS = 13
DOOR_LINTEL_SIDE_EXTEND_UNITS = 0.0
DOOR_TRACK_TEXTURE = "DOORTRAK"
# Door placement offset on room walls: keep clear of corners, allow mild jitter.
DOOR_RANDOM_OFFSET_MAX_FRACTION = 0.35
DOOR_RANDOM_OFFSET_MIN_MARGIN_UNITS = 128.0
MIN_EFFECTIVE_LINTEL_STRIP_DEPTH_UNITS = 1.0
INTERNAL_SECTOR_MIN_EDGE_UNITS = 12.0


class CellXY(NamedTuple):
    x: int
    y: int


class CellOccupancy(IntEnum):
    FREE = 0
    BUFFER = -1
    OCCUPIED = 1


def trace_log_path() -> Path:
    return Path(__file__).resolve().parent / TRACE_LOG_FILENAME


def clear_trace_log() -> None:
    path = trace_log_path()
    try:
        path.write_text("", encoding="utf-8")
    except OSError:
        # If another process holds the file open, keep going and append
        # run headers instead of failing startup.
        return


def set_trace_logging(enabled: bool) -> None:
    global VERBOSE_TRACE_LOG
    VERBOSE_TRACE_LOG = bool(enabled)


def set_trace_map_timer(map_name: str) -> None:
    global TRACE_MAP_START_TIME, TRACE_MAP_NAME
    TRACE_MAP_START_TIME = time.perf_counter()
    TRACE_MAP_NAME = str(map_name)


def clear_trace_map_timer() -> None:
    global TRACE_MAP_START_TIME, TRACE_MAP_NAME
    TRACE_MAP_START_TIME = None
    TRACE_MAP_NAME = ""


def log_trace(message: str) -> None:
    if not VERBOSE_TRACE_LOG:
        return
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3]
    rel = ""
    if TRACE_MAP_START_TIME is not None:
        rel_secs = time.perf_counter() - TRACE_MAP_START_TIME
        rel = f"[+{rel_secs:8.3f}s map={TRACE_MAP_NAME}] "
    try:
        with trace_log_path().open("a", encoding="utf-8") as fh:
            fh.write(f"{ts} {rel}{message}\n")
    except OSError:
        return


def log_event(message: str) -> None:
    # Always persist high-level run/retry/timing events.
    rel = ""
    if TRACE_MAP_START_TIME is not None:
        rel_secs = time.perf_counter() - TRACE_MAP_START_TIME
        rel = f"[+{rel_secs:8.3f}s map={TRACE_MAP_NAME}] "
    log_diag(f"{rel}{message}")
    # Include relative-timing prefixed trace when verbose tracing is enabled.
    log_trace(message)

EXIT_SWITCH_PANEL_WIDTH_UNITS = 64
EXIT_SIGN_ROOM_OFFSET_UNITS = 12
EXIT_SIGN_LONG_UNITS = 32
EXIT_SIGN_DEPTH_UNITS = 8
# EXITSIGN in Doom II is 64x16, so the lowered ceiling delta for the hanging sign is 16.
EXIT_SIGN_TEXTURE_HEIGHT_UNITS = 16

THING_FLAG_EASY = 0x0001
THING_FLAG_MEDIUM = 0x0002
THING_FLAG_HARD = 0x0004
THING_FLAG_AMBUSH = 0x0008
THING_FLAG_MULTI_ONLY = 0x0010

KEY_THING_BY_COLOR = {
    "blue": 5,
    "yellow": 6,
    "red": 13,
}

LOCK_FRAME_TEXTURE_BY_COLOR = {
    "blue": "DOORBLU",
    "yellow": "DOORYEL",
    "red": "DOORRED",
}
DOORFRAME_TRIPLE_TEXTURES = ("DOORRED", "DOORYEL", "DOORBLU")
DOORFRAME_BASE_TEXTURE = "STARTAN3"

DOOM_DOOR_SPECIAL_BY_COLOR = {
    "blue": 26,    # DR Blue Door Open Wait Close
    "yellow": 27,  # DR Yellow Door Open Wait Close
    "red": 28,     # DR Red Door Open Wait Close
}
DOOM_NONKEY_DOOR_SPECIAL = 117  # DR Fast Door Raise (repeatable, no key)
PLAYER_USE_LINE_SPECIALS: frozenset[int] = frozenset(
    {11, DOOM_NONKEY_DOOR_SPECIAL, *DOOM_DOOR_SPECIAL_BY_COLOR.values()}
)

@dataclass(frozen=True)
class Lump:
    name: str
    data: bytes


@dataclass(frozen=True)
class Wad:
    identification: str
    lumps: list[Lump]


@dataclass(frozen=True)
class ThemeStyle:
    room_wall_textures: tuple[str, ...]
    corridor_wall_textures: tuple[str, ...]
    transition_wall_textures: tuple[str, ...]
    door_texture: str
    switch_texture: str
    exit_marker_texture: str
    room_floor: str
    corridor_floor: str
    transition_floor: str
    liquid_floor: str
    ceiling_flat: str
    room_light: int
    corridor_light: int
    transition_light: int


@dataclass(frozen=True)
class EpisodeMapSpec:
    output_map: str
    theme: str
    room_target: int
    map_seed: int


@dataclass(frozen=True)
class RoomRegion:
    cells: tuple[tuple[int, int], ...]
    center: tuple[int, int]


@dataclass(frozen=True)
class GeneratedLayout:
    width: int
    height: int
    terrain: list[list[int]]
    rooms: list[RoomRegion]
    room_index_grid: list[list[int]]
    door_group_grid: list[list[int]]
    corridor_group_grid: list[list[int]]


@dataclass(frozen=True)
class OrientedRoom:
    center: tuple[float, float]
    tangent: tuple[float, float]
    normal: tuple[float, float]
    half_length: float
    half_width: float
    polygon: tuple[tuple[float, float], ...]
    front_left: tuple[float, float]
    front_right: tuple[float, float]
    back_left: tuple[float, float]
    back_right: tuple[float, float]
    side_bulges: dict[str, float]
    l_shape_corner: str | None
    l_shape_cut_length: float
    l_shape_cut_width: float


@dataclass(frozen=True)
class CorridorSection:
    left: tuple[float, float]
    right: tuple[float, float]
    center: tuple[float, float]


@dataclass(frozen=True)
class CorridorStrip:
    sections: tuple[CorridorSection, ...]
    floors: tuple[int, ...]
    wall_texture: str
    start_door_polygon: tuple[tuple[float, float], ...] | None
    end_door_polygon: tuple[tuple[float, float], ...] | None


@dataclass(frozen=True)
class SectorPlan:
    polygon: tuple[tuple[float, float], ...]
    floor_height: int
    ceiling_height: int
    floor_texture: str
    ceiling_texture: str
    light_level: int
    wall_texture: str
    kind: str
    door_edge: int = -1
    door_room: int = -1


@dataclass(frozen=True)
class PolyLayout:
    rooms: list[OrientedRoom]
    corridors: list[CorridorStrip]
    sector_plans: list[SectorPlan]
    connections: list[tuple[int, int]]
    key_sequence: list[tuple[int, str]]
    lock_sequence: list[tuple[int, int, str]]
    room_door_sides: tuple[tuple[str, ...], ...]


@dataclass
class Vertex:
    x: int
    y: int


@dataclass
class Sector:
    floor_height: int
    ceiling_height: int
    floor_texture: str
    ceiling_texture: str
    light_level: int
    special: int
    tag: int


@dataclass
class Sidedef:
    offset_x: int
    offset_y: int
    texture_top: str
    texture_bottom: str
    texture_middle: str
    sector: int
    offset_x_top: int | None = None
    offset_x_bottom: int | None = None
    offset_x_middle: int | None = None
    offset_y_top: int | None = None
    offset_y_bottom: int | None = None
    offset_y_middle: int | None = None


@dataclass
class Linedef:
    v1: int
    v2: int
    flags: int
    special: int
    tag: int
    right: int
    left: int
    arg0: int = 0
    arg1: int = 0
    arg2: int = 0
    arg3: int = 0
    arg4: int = 0


@dataclass
class Thing:
    x: int
    y: int
    angle: int
    thing_type: int
    flags: int


@dataclass
class MutableMap:
    name: str
    vertices: list[Vertex] = field(default_factory=list)
    sectors: list[Sector] = field(default_factory=list)
    sidedefs: list[Sidedef] = field(default_factory=list)
    linedefs: list[Linedef] = field(default_factory=list)
    things: list[Thing] = field(default_factory=list)


@dataclass(frozen=True)
class BuildResult:
    output_path: Path
    map_reports: list[str]
    compatibility_profile: str


@dataclass
class MapPopulationTargets:
    rooms: list[int] = field(default_factory=list)
    platforms: list[tuple[tuple[tuple[float, float], ...], int]] = field(default_factory=list)
    corridors: list[int] = field(default_factory=list)


THEMES: dict[str, ThemeStyle] = {
    "techbase": ThemeStyle(
        room_wall_textures=("STARTAN3", "STARTAN2", "TEKWALL1", "TEKWALL4"),
        corridor_wall_textures=("STARTAN3", "BROWN96", "METAL2"),
        transition_wall_textures=("ASHWALL2", "SUPPORT2", "SUPPORT3"),
        door_texture="BIGDOOR2",
        switch_texture="SW1COMM",
        exit_marker_texture="EXITSIGN",
        room_floor="FLOOR4_8",
        corridor_floor="FLOOR5_2",
        transition_floor="FLOOR5_1",
        liquid_floor="NUKAGE1",
        ceiling_flat="CEIL5_1",
        room_light=168,
        corridor_light=144,
        transition_light=156,
    ),
    "urban": ThemeStyle(
        room_wall_textures=("BRICK7", "BRICK10", "BIGBRIK1", "BIGBRIK2"),
        corridor_wall_textures=("BRICK6", "STONE3", "BROWN144"),
        transition_wall_textures=("ASHWALL2", "GRAYVINE", "WOODMET1"),
        door_texture="BIGDOOR6",
        switch_texture="SW1COMM",
        exit_marker_texture="EXITSIGN",
        room_floor="FLOOR4_8",
        corridor_floor="FLOOR5_2",
        transition_floor="FLOOR5_1",
        liquid_floor="FWATER1",
        ceiling_flat="CEIL5_1",
        room_light=160,
        corridor_light=140,
        transition_light=148,
    ),
    "hellish": ThemeStyle(
        room_wall_textures=("STONE2", "MARBLE1", "MARBLE2", "GSTONE1"),
        corridor_wall_textures=("STONE3", "SP_HOT1", "METAL"),
        transition_wall_textures=("ASHWALL2", "SKINLOW", "SKSNAKE2"),
        door_texture="BIGDOOR7",
        switch_texture="SW1COMM",
        exit_marker_texture="EXITSIGN",
        room_floor="RROCK04",
        corridor_floor="RROCK11",
        transition_floor="RROCK09",
        liquid_floor="BLOOD1",
        ceiling_flat="CEIL5_1",
        room_light=152,
        corridor_light=132,
        transition_light=144,
    ),
}

# Monster & item count controls.
ROOM_MONSTER_BASE_MIN = 1
ROOM_MONSTER_BASE_MAX = 6
ROOM_MONSTER_SCALE = 0.10            # extra per level

CORRIDOR_MONSTER_BASE_MIN = 0
CORRIDOR_MONSTER_BASE_MAX = 3
CORRIDOR_MONSTER_SCALE = 0.05        # extra per level

ROOM_ITEM_BASE_MIN = 4
ROOM_ITEM_BASE_MAX = 7
ROOM_ITEM_SCALE = 0.20               # extra per level

CORRIDOR_ITEM_BASE_MIN = 4
CORRIDOR_ITEM_BASE_MAX = 6
CORRIDOR_ITEM_SCALE = 0.00           # extra per level

MAP_TIER_START = "MAP00"  
MAP_TIER_EARLY = "MAP0X"  
MAP_TIER_MID = "MAP1X"   
MAP_TIER_LATE = "MAP2X"  


# TIER SPAWN TABLES ARE USED FOR DIFFERENT LEVEL RANGES (GRADUALLY)

MAP_TIER_START_MIN = 1
MAP_TIER_START_MID = 2
MAP_TIER_START_MAX = 3

MAP_TIER_EARLY_MIN = 4
MAP_TIER_EARLY_MID = 5
MAP_TIER_EARLY_MAX = 6

MAP_TIER_MID_MIN = 7
MAP_TIER_MID_MID = 10
MAP_TIER_MID_MAX = 13

MAP_TIER_LATE_MIN = 14
MAP_TIER_LATE_MID = 27
MAP_TIER_LATE_MAX = 32


# ACTUAL TIER SPAWN TABLES ITEMS AND DISTRIBUTION

ROOM_MONSTER_WEIGHTS_BY_TIER: dict[str, tuple[tuple[int, int], ...]] = {
    # type, weight
    MAP_TIER_START: (
        (3004, 31),  # Zombieman
        (9, 31),     # Shotgun Guy
        (3001, 31),  # Imp
        (3002, 5),   # Demon
        (58, 2),     # Spectre
    ),
    MAP_TIER_EARLY: (
        (3004, 26),  # Zombieman
        (9, 25),     # Shotgun Guy
        (3001, 25),  # Imp
        (3002, 8),   # Demon
        (58, 6),     # Spectre        
        (65, 10),    # Chaingunner
    ),
    MAP_TIER_MID: (
        (3004, 19),  # Zombieman
        (9, 19),     # Shotgun Guy
        (3001, 19),  # Imp
        (3002, 11),  # Demon
        (58, 8),     # Spectre
        (65, 14),    # Chaingunner
        (3005, 5),   # Cacodemon
        (69, 5),     # Hell Knight
    ),
    MAP_TIER_LATE: (
        (3004, 15),  # Zombieman
        (9, 15),     # Shotgun Guy
        (3001, 15),  # Imp
        (3002, 12),  # Demon
        (58, 8),     # Spectre
        (65, 15),    # Chaingunner
        (3005, 8),   # Cacodemon
        (69, 5),     # Hell Knight
        (66, 2),     # Revenant
        (3003, 2),   # Baron of Hell
        (64, 1),     # Arch-Vile
        (67, 1),     # Mancubus
        (71, 1),     # Pain Elemental
    ),
}

CORRIDOR_MONSTER_WEIGHTS: tuple[tuple[int, int], ...] = (
    (3004, 34),  # zombieman
    (9, 33),     # shotgun guy
    (3001, 33),  # imp
)

# Doom thing radii in map units (used for spawn clearance checks).
MONSTER_RADIUS_BY_THING_TYPE: dict[int, float] = {
    3004: 20.0,  # Zombieman
    9: 20.0,     # Shotgun Guy
    65: 20.0,    # Chaingunner
    3001: 20.0,  # Imp
    66: 20.0,    # Revenant
    64: 20.0,    # Arch-Vile
    69: 24.0,    # Hell Knight
    3003: 24.0,  # Baron of Hell
    3002: 30.0,  # Demon
    58: 30.0,    # Spectre
    3005: 31.0,  # Cacodemon
    71: 31.0,    # Pain Elemental
    67: 48.0,    # Mancubus
}


def monster_spawn_clearance_units(thing_type: int) -> float:
    """Per-side spawn clearance from blockers/walls for a monster type.

    We treat MONSTER_GAP_MARGIN_UNITS as a total extra lane width:
    required_gap = 2*radius + margin. Per-side clearance is half that:
    radius + margin/2.
    """
    radius = MONSTER_RADIUS_BY_THING_TYPE.get(int(thing_type), OBJECT_MIN_SPACING_UNITS)
    return float(radius) + (float(MONSTER_GAP_MARGIN_UNITS) * 0.5)


def monster_collision_radius_units(thing_type: int) -> float | None:
    radius = MONSTER_RADIUS_BY_THING_TYPE.get(int(thing_type))
    if radius is None:
        return None
    return float(radius)

TREASURE_ROOM_REWARD_WEIGHTS: tuple[tuple[int, int], ...] = (
    (2013, 10),  # Soulsphere
    (2023, 10),  # Berserk Pack
    (82, 10),    # Super Shotgun
    (2003, 10),  # Rocket Launcher    
    (2019, 10),  # Blue Armor
    (2006, 5),   # BFG9000
    (8, 10),     # Ammo Backpack
    (83, 10),    # Megasphere
    (2004, 10),  # Plasma Rifle
    
)

ROOM_PICKUP_TABLE_BY_TIER: dict[str, tuple[tuple[int, int], ...]] = {
    MAP_TIER_START: (
        (2011, 10),  # Stimpack
        (2012, 2),   # Medikit
        (2007, 10),  # Ammo Clip
        (2008, 10),  # Shells
        (17, 3),     # Cell Charge
        (2010, 1),   # Rocket
        (2014, 32),  # Health Bonus
        (2015, 32),  # Armor Bonus
        (0, 0),      # No drop
    ),
    MAP_TIER_EARLY: (
        (2011, 10),  # Stimpack
        (2012, 2),   # Medikit
        (2007, 10),  # Ammo Clip
        (2008, 10),  # Shells
        (17, 3),     # Cell Charge
        (2010, 1),   # Rocket
        (2014, 32),  # Health Bonus
        (2015, 32),  # Armor Bonus
        (0, 0),      # No drop
    ),
    MAP_TIER_MID: (
        (2011, 10),  # Stimpack
        (2012, 2),   # Medikit
        (2007, 10),  # Ammo Clip
        (2008, 10),  # Shells
        (17, 3),     # Cell Charge
        (2010, 1),   # Rocket
        (2014, 32),  # Health Bonus
        (2015, 32),  # Armor Bonus
        (0, 0),      # No drop
    ),
    MAP_TIER_LATE: (
        (2011, 10),  # Stimpack
        (2012, 2),   # Medikit
        (2007, 10),  # Ammo Clip
        (2008, 10),  # Shells
        (17, 3),     # Cell Charge
        (2010, 1),   # Rocket
        (2014, 32),  # Health Bonus
        (2015, 32),  # Armor Bonus
        (0, 0),      # No drop
    ),
}

CORRIDOR_PICKUP_TABLE_BY_TIER: dict[str, tuple[tuple[int, int], ...]] = {
    MAP_TIER_START: (
        (2014, 25),  # Health Bonus
        (2015, 50),  # Armor Bonus
        (0, 0),      # No drop
    ),
    MAP_TIER_EARLY: (
        (2014, 25),  # Health Bonus
        (2015, 50),  # Armor Bonus
        (0, 0),      # No drop
    ),
    MAP_TIER_MID: (
        (2014, 25),  # Health Bonus
        (2015, 50),  # Armor Bonus
        (0, 0),      # No drop
    ),
    MAP_TIER_LATE: (
        (2014, 25),  # Health Bonus
        (2015, 50),  # Armor Bonus
        (0, 0),      # No drop
    ),
}

# Theme-specific decorative things. Deliberately excludes special uniques (e.g., Romero's head, type 87).
DECOR_POOL_BY_THEME: dict[str, tuple[int, ...]] = {
    "techbase": (
        24,                  # pool of blood and bones
        30, 31,              # green marble pillars
        34,                  # candles
        35,                  # candelabra
        44, 45, 46,          # tall torch set
        79, 80,              # blood pools
        85, 86,              # tech lamps
    ),
    "urban": (
        24,                  # pool of blood and bones
        30, 31,              # green pillars
        34,                  # candles
        35,                  # candelabra
        43,                  # burning barrel
        44, 45, 46, 47,      # torch / stalagmite set
        79, 80,              # blood pools
    ),
    "hellish": (
        24, 25, 26,          # blood/impaled variants
        27, 28, 29,          # skull decorations
        32,                  # red pillar
        34,                  # candles
        35,                  # candelabra
        42, 43, 44, 45, 46,  # torch set + burning barrel
        54,                  # hanging leg
        59, 61, 62, 63,      # hanging gore set
        73, 74, 75, 76, 77,  # additional hanging decorations
        79, 80,              # blood pools
    ),
}

# Small decorations suitable for platform tops.
SMALL_PLATFORM_DECOR_BY_THEME: dict[str, tuple[int, ...]] = {
    "techbase": (
        34,          # candles
        79, 80,      # blood
    ),
    "urban": (
        34,          # candles
        79, 80,      # blood
    ),
    "hellish": (
        #24,          # pool of blood and bones
        34,          # candles
        79, 80,      # blood
        #55, 56, 57,  # short torches
    ),
}

# Theme-specific one-off vertical wall strip textures (texture name, native width in map units).
ROOM_COLUMN_TEXTURES_BY_THEME: dict[str, tuple[tuple[str, int], ...]] = {
    "techbase": (
        ("SUPPORT3", 64),
        ("PANEL4", 64),
        ("LITE5", 16),
        ("SUPPORT2", 64),
        ("LITE3", 32),
        ("TEKGREN5", 64),
        ("TEKGREN3", 64),
        ("TEKGREN4", 64),
    ),
    "urban": (
        ("BSTONE3", 64),
        ("PANBOOK", 64),
        ("PANEL4", 64),
        ("PANBLACK", 64),
    ),
    "hellish": (
        ("MARBFACE", 128),
        ("GSTGARG", 64),
        ("GSTSATYR", 64),
        ("GSTLION", 64),
        ("GSTFONT3", 64),
        ("GSTFONT1", 64),
        ("GSTFONT2", 64),
        ("SKINSYMB", 256),
    ),
}

# Compatible base wall textures -> decorative column textures.
# Ordered by confidence; earlier entries are preferred during placement.
COLUMN_GROUPS_BY_THEME: dict[str, tuple[tuple[str, tuple[str, ...]], ...]] = {
    "techbase": (
        ("BLAKWAL2", ("BLAKWAL1",)),
        ("COMPBLUE", ("COMPSPAN", "COMPSTA1", "COMPSTA2")),
        ("COMPSTA1", ("COMPSTA2",)),
        ("COMPTALL", ("COMPWERD",)),
        ("GRAY1", ("GRAY4", "GRAYBIG")),
        ("PIPEWAL2", ("PIPEWAL1",)),
        ("SHAWN2", ("SHAWN1",)),
        ("SILVER1", ("SILVER2", "SILVER3")),
        ("STARTAN2", ("LITE5", "SUPPORT2", "LITE3")),
        ("STARTAN3", ("LITE5", "SUPPORT2", "LITE3")),
        ("TEKWALL1", ("SUPPORT3",)),
        ("TEKWALL4", ("SUPPORT3",)),
        ("METAL2", ("SUPPORT3",)),
        ("SUPPORT2", ("LITE5", "LITE3")),
        ("TEKGREN2", ("TEKGREN5", "TEKGREN3", "TEKGREN4", "LITE5", "LITE3", "TEKGREN1")),
    ),
    "urban": (
        ("BIGBRIK1", ("BIGBRIK3",)),
        ("BRICK1", ("BRICK5", "BRICKLIT", "BRWINDOW")),
        ("BRICK4", ("BRICK3",)),
        ("BRICK6", ("BRICK8", "BRICK9")),
        ("BRONZE1", ("BRONZE2", "BRONZE3", "BRONZE4")),
        ("BROWNGRN", ("BRNPOIS",)),
        ("BSTONE2", ("BSTONE3",)),
        ("CEMENT1", ("CEMENT2", "CEMENT5", "CEMENT6")),
        ("CEMENT7", ("CEMENT8",)),
        ("ICKWALL1", ("ICKWALL2",)),
        ("ICKWALL2", ("ICKWALL4",)),
        ("ICKWALL3", ("ICKWALL4", "ICKWALL7")),
        ("METAL2", ("METAL3", "METAL4", "METAL5", "METAL6")),
        ("MODWALL1", ("MODWALL2",)),
        ("NUKEDGE1", ("NUKEPOIS",)),
        ("PANCASE2", ("PANBOOK", "PANBORD1", "PANBORD2", "PANCASE1")),
        ("PANEL4", ("PANBOOK", "PANEL1", "PANBLACK")),
        ("PANEL6", ("PANEL7", "PANEL8", "PANEL9")),
        ("PIPE2", ("PIPE4",)),
        ("SLADWALL", ("SLADPOIS",)),
        ("STARG1", ("STARG2", "STARG3")),
        ("STARGR1", ("STARGR2",)),
        ("STONE2", ("STONE3",)),
        ("STONE4", ("STONE5",)),
        ("STUCCO1", ("STUCCO2", "STUCCO3")),
        ("WOOD1", ("WOOD3",)),
        ("WOOD8", ("WOOD9", "WOOD7")),
    ),
    "hellish": (
        ("FIREWALL", ("FIREWALA",)),
        ("GSTONE1", ("GSTSATYR", "GSTLION", "GSTGARG", "MARBFACE")),
        ("GSTONE2", ("GSTFONT2",)),
        ("MARBLE1", ("MARBFACE", "GSTGARG", "MARBFAC2", "MARBFAC3")),
        ("MARBLE2", ("MARBFACE",)),
        ("MARBLE3", ("MARBFAC3",)),
        ("MARBGRAY", ("MARBFAC4",)),
        ("SKINMET1", ("SKINSYMB",)),
        ("SKINMET2", ("SKINMET1", "SKINSCAB", "SKINSYMB")),
        ("WOOD1", ("WOODGARG",)),
    ),
}

# Native widths for candidate wall-column insert textures.
# Default is 64 when a texture is not explicitly listed.
COLUMN_TEXTURE_WIDTH_UNITS: dict[str, int] = {
    "LITE5": 16,
    "LITE3": 32,
    "COMPSPAN": 32,
    "PANBORD1": 32,
    "PANBORD2": 16,
    "MARBFACE": 128,
    "MARBFAC2": 128,
    "MARBFAC3": 128,
    "BRICK5": 128,
    "BRNPOIS": 128,
    "CEMENT2": 128,
    "CEMENT5": 128,
    "CEMENT6": 128,
    "COMPSTA1": 128,
    "COMPSTA2": 128,
    "FIREWALA": 128,
    "GRAYBIG": 128,
    "NUKEPOIS": 128,
    "SHAWN1": 128,
    "STARGR2": 128,
    "STARG2": 128,
    "STARG3": 128,
    "STONE3": 128,
    "PIPE4": 256,
    "SKINMET1": 256,
    "SKINSCAB": 256,
    "SKINSYMB": 256,
    "WOOD3": 256,
}
TEXTURE_WIDTH_FALLBACK_UNITS = 64
_TEXTURE_WIDTH_BY_NAME_CACHE: dict[str, int] | None = None


def load_texture_width_catalog() -> dict[str, int]:
    """Load texture widths from optional extracted-texture manifest."""
    global _TEXTURE_WIDTH_BY_NAME_CACHE
    if _TEXTURE_WIDTH_BY_NAME_CACHE is not None:
        return _TEXTURE_WIDTH_BY_NAME_CACHE

    widths: dict[str, int] = {}
    manifest_path = Path(__file__).resolve().parent / "textures_png" / "textures_manifest.csv"
    if manifest_path.exists():
        try:
            with manifest_path.open("r", encoding="utf-8", newline="") as fh:
                reader = csv.DictReader(fh)
                for row in reader:
                    texture_name = str(row.get("texture_name", "")).strip().upper()
                    width_raw = str(row.get("width", "")).strip()
                    if not texture_name or not width_raw:
                        continue
                    try:
                        width = int(width_raw)
                    except ValueError:
                        continue
                    if width > 0 and texture_name not in widths:
                        widths[texture_name] = width
        except OSError:
            widths = {}

    _TEXTURE_WIDTH_BY_NAME_CACHE = widths
    return _TEXTURE_WIDTH_BY_NAME_CACHE


def texture_width_for_alignment(texture_name: str) -> int:
    """Best-effort wall texture width used for modulo-safe offset alignment."""
    name = str(texture_name).strip().upper()
    if not name or name == "-":
        return TEXTURE_WIDTH_FALLBACK_UNITS
    if name in COLUMN_TEXTURE_WIDTH_UNITS:
        return int(COLUMN_TEXTURE_WIDTH_UNITS[name])
    catalog = load_texture_width_catalog()
    width = int(catalog.get(name, TEXTURE_WIDTH_FALLBACK_UNITS))
    return max(1, width)

TITLE_ARTICLES: tuple[str, ...] = ("The","The")
TITLE_ADJECTIVES_BY_THEME: dict[str, tuple[str, ...]] = {
    "techbase": (
        "Darkened",
        "Hushed",
        "Perilous",
        "Forbidden",
        "Sealed",
        "Shattered",
        "Forsaken",
        "Rustbound",
        "Silent",
        "Buried",
    ),
    "urban": (
        "Cursed",
        "Gruesome",
        "Perilous",
        "Hollow",
        "Forsaken",
        "Blighted",
        "Sundered",
        "Ashen",
        "Withered",
        "Hushed",
    ),
    "hellish": (
        "Hellish",
        "Cursed",
        "Forbidden",
        "Infernal",
        "Dreaded",
        "Blighted",
        "Gruesome",
        "Baleful",
        "Profane",
        "Ravaged",
    ),
}
TITLE_PLACE_BY_THEME: dict[str, tuple[str, ...]] = {
    "techbase": ("Base", "Complex", "Facility", "Mine", "Refinery", "Depot", "Station", "Foundry"),
    "urban": ("Block", "District", "Cellar", "Bastion", "Keep", "Vault", "Catacomb", "Quarter"),
    "hellish": ("Pit", "Dungeon", "Crypt", "Sanctum", "Abyss", "Temple", "Catacomb", "Chasm"),
}
TITLE_OF_SUFFIXES: tuple[str, ...] = (
    "Suffering",
    "Despair",
    "Carnage",
    "Remorse",
    "Torment",
    "Agony",
    "Ruin",
    "Ashes",
    "Shadows",
    "Damnation",
)
CAMPAIGN_TITLE = "Rogue Doom"


def default_episode_plan(base_seed: int | None = None) -> list[EpisodeMapSpec]:
    if base_seed is None:
        base_seed = default_daily_seed()
    plan_rng = random.Random(base_seed ^ 0xA5A55A5A)
    map_seed_stride = 1000003

    def choose_weighted_theme(map_num: int) -> str:
        tier = map_tier_from_number(map_num)
        if tier in {MAP_TIER_START, MAP_TIER_EARLY}:
            weights = (("techbase", 0.5), ("urban", 0.3), ("hellish", 0.2))
        elif tier == MAP_TIER_MID:
            weights = (("techbase", 0.2), ("urban", 0.5), ("hellish", 0.3))
        else:
            weights = (("techbase", 0.3), ("urban", 0.2), ("hellish", 0.5))
        roll = plan_rng.random()
        acc = 0.0
        for theme_name, chance in weights:
            acc += chance
            if roll < acc:
                return theme_name
        return weights[-1][0]

    specs: list[EpisodeMapSpec] = []
    for map_num in range(1, 33):
        if map_num<4:
            theme = ["techbase", "urban", "hellish"][(map_num-1)%3]
        else:
            theme = choose_weighted_theme(map_num)
        
        room_target = 10
        specs.append(
            EpisodeMapSpec(
                output_map=f"MAP{map_num:02d}",
                theme=theme,            
                room_target=room_target,
                map_seed=base_seed + (map_num * map_seed_stride) + 55,
            )
        )    
    return specs[:]


def map_number_from_name(map_name: str) -> int | None:
    value = map_name.strip().upper()
    if not value.startswith("MAP") or len(value) != 5:
        return None
    if not value[3:].isdigit():
        return None
    number = int(value[3:])
    if number < 1 or number > 99:
        return None
    return number


def map_tier_from_number(map_num: int) -> str:
    if MAP_TIER_START_MIN <= map_num <= MAP_TIER_START_MAX:
        return MAP_TIER_START
    if MAP_TIER_EARLY_MIN <= map_num <= MAP_TIER_EARLY_MAX:
        return MAP_TIER_EARLY
    if MAP_TIER_MID_MIN <= map_num <= MAP_TIER_MID_MAX:
        return MAP_TIER_MID
    return MAP_TIER_LATE


def map_tier_from_name(map_name: str) -> str:
    map_num = map_number_from_name(map_name)
    if map_num is None:
        return MAP_TIER_LATE
    return map_tier_from_number(map_num)


TIER_MID_ANCHORS: tuple[tuple[str, int], ...] = (
    (MAP_TIER_START, MAP_TIER_START_MID),
    (MAP_TIER_EARLY, MAP_TIER_EARLY_MID),
    (MAP_TIER_MID, MAP_TIER_MID_MID),
    (MAP_TIER_LATE, MAP_TIER_LATE_MID),
)


def tier_blend_for_map_number(map_num: int) -> tuple[str, str, float]:
    m = max(1, int(map_num))
    first_tier, first_mid = TIER_MID_ANCHORS[0]
    if m <= first_mid:
        return first_tier, first_tier, 0.0
    for idx in range(len(TIER_MID_ANCHORS) - 1):
        low_tier, low_mid = TIER_MID_ANCHORS[idx]
        high_tier, high_mid = TIER_MID_ANCHORS[idx + 1]
        if m <= high_mid:
            span = max(1, high_mid - low_mid)
            t = (float(m) - float(low_mid)) / float(span)
            t = max(0.0, min(1.0, t))
            return low_tier, high_tier, t
    last_tier, _last_mid = TIER_MID_ANCHORS[-1]
    return last_tier, last_tier, 0.0


def pick_tier_table_by_map_number(
    map_num: int,
    table_by_tier: dict[str, tuple[tuple[int, int], ...]],
    rng: random.Random,
) -> tuple[tuple[int, int], ...]:
    low_tier, high_tier, high_prob = tier_blend_for_map_number(map_num)
    if low_tier == high_tier:
        chosen_tier = low_tier
    else:
        chosen_tier = high_tier if rng.random() < high_prob else low_tier
    if chosen_tier not in table_by_tier:
        available = ", ".join(sorted(table_by_tier.keys()))
        raise ValueError(
            f"Missing tier table '{chosen_tier}' for map {map_num}. "
            f"Available tiers: {available}"
        )
    return table_by_tier[chosen_tier]


def procedural_level_title(theme_name: str, rng: random.Random) -> str:
    adjs = TITLE_ADJECTIVES_BY_THEME.get(theme_name, TITLE_ADJECTIVES_BY_THEME["urban"])
    places = TITLE_PLACE_BY_THEME.get(theme_name, TITLE_PLACE_BY_THEME["urban"])
    article = rng.choice(TITLE_ARTICLES)
    adjective = rng.choice(adjs)
    place = rng.choice(places)
    suffix = rng.choice(TITLE_OF_SUFFIXES)
    return f"{article} {adjective} {place}"  # of {suffix}


def build_procedural_level_titles(specs: list[EpisodeMapSpec]) -> dict[str, str]:
    titles: dict[str, str] = {}
    used: set[str] = set()
    for spec in specs:
        title_rng = random.Random((spec.map_seed * 2147483647) ^ 0xC0DECAFE)
        name = ""
        for _ in range(64):
            candidate = procedural_level_title(spec.theme, title_rng)
            if candidate not in used:
                name = candidate
                break
        if not name:
            map_num = map_number_from_name(spec.output_map) or 0
            name = f"{procedural_level_title(spec.theme, title_rng)} {map_num:02d}"
        used.add(name)
        titles[spec.output_map.upper()] = name
    return titles


def encode_mapinfo_level_names(specs: list[EpisodeMapSpec]) -> bytes:
    titles = build_procedural_level_titles(specs)
    parts: list[str] = []
    if specs:
        first_map = specs[0].output_map.upper()
        parts.append("clearepisodes\n")
        parts.append(f"episode {first_map}\n")
        parts.append("{\n")
        parts.append(f'    name = "{CAMPAIGN_TITLE}"\n')
        parts.append("}\n\n")
    for idx, spec in enumerate(specs):
        map_name = spec.output_map.upper()
        level_name = titles.get(map_name, map_name)
        level_name = level_name.replace('"', "")
        if idx + 1 < len(specs):
            next_map = specs[idx + 1].output_map.upper()
        parts.append(f'map {map_name} "{level_name}"\n')
        parts.append("{\n")
        if idx + 1 < len(specs):
            parts.append(f'    next = "{next_map}"\n')
        else:
            # End the episode cleanly instead of wrapping MAP32 -> MAP01.
            parts.append('    next = "EndGameC"\n')
        parts.append('    sky1 = "SKY1", 0.0\n')
        parts.append("}\n\n")
    return "".join(parts).encode("utf-8")


def encode_animdefs() -> bytes:
    # Explicit flat animations for liquids used by this generator.
    # This keeps water/blood movement consistent in GZDoom even if IWAD defaults vary.
    lines = [
        "flat FWATER1",
        "pic 1 tics 8",
        "pic 2 tics 8",
        "pic 3 tics 8",
        "pic 4 tics 8",
        "",
        "flat BLOOD1",
        "pic 1 tics 8",
        "pic 2 tics 8",
        "pic 3 tics 8",
        "",
        "flat NUKAGE1",
        "pic 1 tics 8",
        "pic 2 tics 8",
        "pic 3 tics 8",
        "",
        "flat LAVA1",
        "pic 1 tics 8",
        "pic 2 tics 8",
        "pic 3 tics 8",
        "pic 4 tics 8",
        "",
        "flat DBRAIN1",
        "pic 1 tics 8",
        "pic 2 tics 8",
        "pic 3 tics 8",
        "pic 4 tics 8",
        "",
    ]
    return "\n".join(lines).encode("ascii")


def normalize_lump_name(name: str) -> str:
    value = name.strip().upper()
    if not value:
        raise ValueError("Lump name cannot be empty.")
    if len(value) > 8:
        raise ValueError(f"Lump name '{name}' exceeds 8 characters.")
    if not value.isascii():
        raise ValueError(f"Lump name '{name}' must be ASCII.")
    return value


def encode_lump_name(name: str) -> bytes:
    return normalize_lump_name(name).encode("ascii").ljust(8, b"\x00")


def weighted_pick(weighted: Iterable[tuple[int, int]], rng: random.Random) -> int:
    items = [(value, max(0, int(weight))) for value, weight in weighted]
    total = sum(weight for _value, weight in items)
    if total <= 0:
        return items[0][0]
    roll = rng.randrange(total)
    acc = 0
    for value, weight in items:
        acc += weight
        if roll < acc:
            return value
    return items[-1][0]


def write_wad(path: Path, wad: Wad) -> None:
    ident = wad.identification.upper()
    if ident not in {"IWAD", "PWAD"}:
        raise ValueError("WAD type must be IWAD or PWAD.")

    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("wb") as handle:
        handle.write(WAD_HEADER.pack(ident.encode("ascii"), len(wad.lumps), 0))

        directory: list[tuple[int, int, str]] = []
        for lump in wad.lumps:
            lump_name = normalize_lump_name(lump.name)
            lump_pos = handle.tell()
            if lump.data:
                handle.write(lump.data)
            directory.append((lump_pos, len(lump.data), lump_name))

        directory_offset = handle.tell()
        for lump_pos, lump_size, lump_name in directory:
            handle.write(WAD_DIRECTORY_ENTRY.pack(lump_pos, lump_size, encode_lump_name(lump_name)))

        handle.seek(0)
        handle.write(WAD_HEADER.pack(ident.encode("ascii"), len(wad.lumps), directory_offset))


def try_build_znodes_with_zdbsp(wad_path: Path) -> tuple[bool, str]:
    """Best-effort post-pass to embed ZNODES via zdbsp when available."""
    zdbsp = shutil.which("zdbsp") or shutil.which("zdbsp.exe")
    if not zdbsp:
        cwd_tool = Path.cwd() / "zdbsp.exe"
        if cwd_tool.exists():
            zdbsp = str(cwd_tool)
    if not zdbsp:
        local_tool = Path(__file__).resolve().parent / "tools" / "zdbsp.exe"
        if local_tool.exists():
            zdbsp = str(local_tool)
    if not zdbsp:
        return False, "zdbsp_not_found"

    tmp_out = wad_path.with_suffix(wad_path.suffix + ".zdbsp_tmp")
    if tmp_out.exists():
        try:
            tmp_out.unlink()
        except OSError:
            pass
    cmd = [zdbsp, "-X", "-o", str(tmp_out), str(wad_path)]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    if proc.returncode != 0:
        stderr = (proc.stderr or "").strip().replace("\r", " ").replace("\n", " ")
        stdout = (proc.stdout or "").strip().replace("\r", " ").replace("\n", " ")
        msg = stderr or stdout or f"exit_{proc.returncode}"
        if tmp_out.exists():
            try:
                tmp_out.unlink()
            except OSError:
                pass
        return False, f"zdbsp_failed:{msg[:220]}"
    if not tmp_out.exists():
        return False, "zdbsp_missing_tmp_output"
    try:
        tmp_out.replace(wad_path)
    except OSError as exc:
        return False, f"replace_failed:{exc}"
    return True, "zdbsp_ok"


def largest_component(cells: set[tuple[int, int]]) -> set[tuple[int, int]]:
    if not cells:
        return set()
    remaining = set(cells)
    best: set[tuple[int, int]] = set()

    while remaining:
        start = next(iter(remaining))
        queue = deque([start])
        component = {start}
        remaining.remove(start)
        while queue:
            x, y = queue.popleft()
            for nx, ny in ((x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)):
                if (nx, ny) in remaining:
                    remaining.remove((nx, ny))
                    component.add((nx, ny))
                    queue.append((nx, ny))
        if len(component) > len(best):
            best = component
    return best


def normalize_cells(cells: Iterable[tuple[int, int]]) -> set[tuple[int, int]]:
    values = list(cells)
    if not values:
        return set()
    min_x = min(x for x, _ in values)
    min_y = min(y for _, y in values)
    return {(x - min_x, y - min_y) for x, y in values}


def make_room_shape(rng: random.Random, width: int, height: int) -> set[tuple[int, int]]:
    base = {(x, y) for x in range(width) for y in range(height)}
    style = rng.choice(("rect", "chamfer", "lshape", "twin"))

    if style == "rect":
        shaped = base
    elif style == "chamfer":
        shaped = set(base)
        cut = max(1, min(width, height) // 4)
        for i in range(cut):
            shaped.discard((i, i))
            shaped.discard((width - 1 - i, i))
            shaped.discard((i, height - 1 - i))
            shaped.discard((width - 1 - i, height - 1 - i))
    elif style == "lshape":
        shaped = set(base)
        cut_w = rng.randint(max(2, width // 3), max(2, width // 2))
        cut_h = rng.randint(max(2, height // 3), max(2, height // 2))
        corner = rng.choice(("nw", "ne", "sw", "se"))
        for x in range(cut_w):
            for y in range(cut_h):
                if corner == "nw":
                    shaped.discard((x, y))
                elif corner == "ne":
                    shaped.discard((width - 1 - x, y))
                elif corner == "sw":
                    shaped.discard((x, height - 1 - y))
                else:
                    shaped.discard((width - 1 - x, height - 1 - y))
    else:
        shaped = set()
        w1 = max(4, width - rng.randint(0, 3))
        h1 = max(4, height - rng.randint(0, 3))
        w2 = max(4, width - rng.randint(0, 3))
        h2 = max(4, height - rng.randint(0, 3))
        ox = rng.randint(-(w2 // 3), max(1, w1 // 3))
        oy = rng.randint(-(h2 // 3), max(1, h1 // 3))
        for x in range(w1):
            for y in range(h1):
                shaped.add((x, y))
        for x in range(w2):
            for y in range(h2):
                shaped.add((x + ox, y + oy))

    shaped = largest_component(normalize_cells(shaped))
    if len(shaped) < 18:
        return {(x, y) for x in range(width) for y in range(height)}
    return shaped


def center_of_cells(cells: Iterable[tuple[int, int]]) -> tuple[int, int]:
    points = list(cells)
    avg_x = sum(x for x, _ in points) / len(points)
    avg_y = sum(y for _, y in points) / len(points)
    return min(points, key=lambda p: (p[0] - avg_x) ** 2 + (p[1] - avg_y) ** 2)


def can_place_room(
    terrain: list[list[int]],
    room_cells: set[tuple[int, int]],
    anchor_x: int,
    anchor_y: int,
    margin: int = 1,
) -> bool:
    h = len(terrain)
    w = len(terrain[0])
    absolute = {(anchor_x + x, anchor_y + y) for x, y in room_cells}

    for x, y in absolute:
        if x < 2 or y < 2 or x >= w - 2 or y >= h - 2:
            return False
    for x, y in absolute:
        for ny in range(y - margin, y + margin + 1):
            for nx in range(x - margin, x + margin + 1):
                if nx < 0 or ny < 0 or nx >= w or ny >= h:
                    return False
                if terrain[ny][nx] != EMPTY and (nx, ny) not in absolute:
                    return False
    return True


def place_rooms(
    terrain: list[list[int]],
    rng: random.Random,
    target_rooms: int,
) -> list[RoomRegion]:
    h = len(terrain)
    w = len(terrain[0])
    rooms: list[RoomRegion] = []
    attempts = 0
    while len(rooms) < target_rooms and attempts < 1200:
        attempts += 1
        rw = rng.randint(6, 12)
        rh = rng.randint(5, 10)
        shape = make_room_shape(rng, rw, rh)
        max_x = max(x for x, _ in shape)
        max_y = max(y for _, y in shape)
        if max_x + 4 >= w or max_y + 4 >= h:
            continue
        anchor_x = rng.randint(2, w - max_x - 3)
        anchor_y = rng.randint(2, h - max_y - 3)
        if not can_place_room(terrain, shape, anchor_x, anchor_y, margin=1):
            continue

        absolute = {(anchor_x + x, anchor_y + y) for x, y in shape}
        for x, y in absolute:
            terrain[y][x] = ROOM
        center = center_of_cells(absolute)
        rooms.append(
            RoomRegion(
                cells=tuple(sorted(absolute)),
                center=center,
            )
        )
    return rooms


def corridor_edges(rooms: list[RoomRegion], rng: random.Random) -> list[tuple[int, int]]:
    if len(rooms) < 2:
        return []

    centers = [room.center for room in rooms]
    connected = {0}
    edges: list[tuple[int, int]] = []

    while len(connected) < len(rooms):
        best: tuple[int, int] | None = None
        best_dist = 10**9
        for i in connected:
            x1, y1 = centers[i]
            for j in range(len(rooms)):
                if j in connected:
                    continue
                x2, y2 = centers[j]
                dist = abs(x1 - x2) + abs(y1 - y2)
                if dist < best_dist:
                    best_dist = dist
                    best = (i, j)
        if best is None:
            break
        edges.append(best)
        connected.add(best[1])

    edge_set = {tuple(sorted(edge)) for edge in edges}
    candidates: list[tuple[int, int, int]] = []
    for i in range(len(rooms)):
        for j in range(i + 1, len(rooms)):
            if (i, j) in edge_set:
                continue
            x1, y1 = centers[i]
            x2, y2 = centers[j]
            dist = abs(x1 - x2) + abs(y1 - y2)
            candidates.append((dist, i, j))
    candidates.sort(key=lambda item: item[0])

    extra_target = max(1, len(rooms) // 4)
    for _dist, i, j in candidates:
        if extra_target <= 0:
            break
        if rng.random() < 0.35:
            edges.append((i, j))
            extra_target -= 1

    return edges


def carve_brush(terrain: list[list[int]], x: int, y: int, width: int) -> None:
    h = len(terrain)
    w = len(terrain[0])
    radius = max(0, width // 2)
    for ny in range(y - radius, y + radius + 1):
        for nx in range(x - radius, x + radius + 1):
            if nx < 1 or ny < 1 or nx >= w - 1 or ny >= h - 1:
                continue
            if abs(nx - x) + abs(ny - y) > radius + 1:
                continue
            if terrain[ny][nx] == ROOM:
                continue
            if terrain[ny][nx] == EMPTY:
                terrain[ny][nx] = CORRIDOR


def carve_segment(
    terrain: list[list[int]],
    x1: float,
    y1: float,
    x2: float,
    y2: float,
    width: int,
) -> None:
    dx = x2 - x1
    dy = y2 - y1
    steps = max(1, int(math.ceil(max(abs(dx), abs(dy)) * 2.0)))
    last: tuple[int, int] | None = None
    for i in range(steps + 1):
        t = i / steps
        cx = int(round(x1 + dx * t))
        cy = int(round(y1 + dy * t))
        if last == (cx, cy):
            continue
        last = (cx, cy)
        carve_brush(terrain, cx, cy, width)


def connect_rooms_with_corridor(
    terrain: list[list[int]],
    a: tuple[int, int],
    b: tuple[int, int],
    width: int,
    rng: random.Random,
) -> None:
    x1, y1 = a
    x2, y2 = b
    # True angled corridor centerline (no axis-only bends).
    carve_segment(terrain, float(x1), float(y1), float(x2), float(y2), width)


def terrain_at(terrain: list[list[int]], x: int, y: int) -> int:
    if y < 0 or y >= len(terrain) or x < 0 or x >= len(terrain[0]):
        return EMPTY
    return terrain[y][x]


def mark_transition_zones(terrain: list[list[int]]) -> list[list[int]]:
    h = len(terrain)
    w = len(terrain[0])
    updated = [row[:] for row in terrain]
    for y in range(h):
        for x in range(w):
            if terrain[y][x] != CORRIDOR:
                continue
            for nx, ny in ((x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)):
                if terrain_at(terrain, nx, ny) == ROOM:
                    updated[y][x] = TRANSITION
                    break
    return updated


def doorway_axis(terrain: list[list[int]], x: int, y: int) -> str | None:
    if terrain[y][x] != TRANSITION:
        return None

    north = terrain_at(terrain, x, y - 1)
    south = terrain_at(terrain, x, y + 1)
    west = terrain_at(terrain, x - 1, y)
    east = terrain_at(terrain, x + 1, y)

    vertical_split = (
        (north == ROOM and south == CORRIDOR)
        or (south == ROOM and north == CORRIDOR)
    )
    horizontal_split = (
        (west == ROOM and east == CORRIDOR)
        or (east == ROOM and west == CORRIDOR)
    )

    if vertical_split and not horizontal_split:
        return "h"
    if horizontal_split and not vertical_split:
        return "v"
    return None


def contiguous_runs(values: list[int]) -> list[list[int]]:
    if not values:
        return []
    numbers = sorted(set(values))
    runs: list[list[int]] = []
    current = [numbers[0]]
    for value in numbers[1:]:
        if value == current[-1] + 1:
            current.append(value)
        else:
            runs.append(current)
            current = [value]
    runs.append(current)
    return runs


def place_doorways(
    terrain: list[list[int]],
    rng: random.Random,
) -> list[list[int]]:
    h = len(terrain)
    w = len(terrain[0]) if h > 0 else 0
    horizontal: dict[int, list[int]] = {}
    vertical: dict[int, list[int]] = {}

    for y in range(h):
        for x in range(w):
            axis = doorway_axis(terrain, x, y)
            if axis == "h":
                horizontal.setdefault(y, []).append(x)
            elif axis == "v":
                vertical.setdefault(x, []).append(y)

    segments: list[tuple[str, list[tuple[int, int]]]] = []
    for y, xs in horizontal.items():
        for run in contiguous_runs(xs):
            segments.append(("h", [(x, y) for x in run]))
    for x, ys in vertical.items():
        for run in contiguous_runs(ys):
            segments.append(("v", [(x, y) for y in run]))

    if not segments:
        return [[-1 for _ in range(w)] for _ in range(h)]

    rng.shuffle(segments)
    target_count = max(2, len(segments) // 3)
    selected = segments[:target_count]

    door_group_grid = [[-1 for _ in range(w)] for _ in range(h)]
    group_id = 0
    walkable = {ROOM, CORRIDOR, TRANSITION, DOOR}
    for axis, segment in selected:
        if not segment:
            continue

        if axis == "h":
            ordered = sorted(segment, key=lambda item: item[0])
        else:
            ordered = sorted(segment, key=lambda item: item[1])
        if len(ordered) < DOOR_WIDTH_CELLS:
            continue
        start = (len(ordered) - DOOR_WIDTH_CELLS) // 2
        door_cells = ordered[start:start + DOOR_WIDTH_CELLS]
        if len(door_cells) != DOOR_WIDTH_CELLS:
            continue
        if any(not (0 <= x < w and 0 <= y < h and terrain[y][x] == TRANSITION) for x, y in door_cells):
            continue

        segment_set = set(segment)
        door_set = set(door_cells)

        def projected(nx: int, ny: int) -> int:
            if nx < 0 or ny < 0 or nx >= w or ny >= h:
                return EMPTY
            if (nx, ny) in segment_set and (nx, ny) not in door_set:
                return EMPTY
            if (nx, ny) in door_set:
                return DOOR
            return terrain[ny][nx]

        valid = True
        for x, y in door_cells:
            n = projected(x, y - 1)
            s = projected(x, y + 1)
            wv = projected(x - 1, y)
            e = projected(x + 1, y)
            if axis == "h":
                room_corr = ((n == ROOM and s == CORRIDOR) or (s == ROOM and n == CORRIDOR))
                side_ok = (wv in {EMPTY, DOOR}) and (e in {EMPTY, DOOR})
            else:
                room_corr = ((wv == ROOM and e == CORRIDOR) or (e == ROOM and wv == CORRIDOR))
                side_ok = (n in {EMPTY, DOOR}) and (s in {EMPTY, DOOR})
            if not room_corr or not side_ok:
                valid = False
                break
            neighbors = (n, s, wv, e)
            other_walkable = sum(1 for value in neighbors if value in walkable and value not in {ROOM, CORRIDOR, DOOR})
            if other_walkable != 0:
                valid = False
                break
        if not valid:
            continue

        for x, y in segment:
            if (x, y) in door_set:
                continue
            if 0 <= x < w and 0 <= y < h and terrain[y][x] == TRANSITION:
                terrain[y][x] = EMPTY

        for x, y in door_cells:
            terrain[y][x] = DOOR
            door_group_grid[y][x] = group_id
        group_id += 1
    return door_group_grid


def build_corridor_group_grid(terrain: list[list[int]]) -> list[list[int]]:
    h = len(terrain)
    w = len(terrain[0]) if h > 0 else 0
    groups = [[-1 for _ in range(w)] for _ in range(h)]
    queue: deque[tuple[int, int]] = deque()
    group_id = 0

    for y in range(h):
        for x in range(w):
            if terrain[y][x] != CORRIDOR or groups[y][x] >= 0:
                continue
            groups[y][x] = group_id
            queue.append((x, y))
            while queue:
                cx, cy = queue.popleft()
                for nx, ny in ((cx - 1, cy), (cx + 1, cy), (cx, cy - 1), (cx, cy + 1)):
                    if nx < 0 or ny < 0 or nx >= w or ny >= h:
                        continue
                    if terrain[ny][nx] != CORRIDOR or groups[ny][nx] >= 0:
                        continue
                    groups[ny][nx] = group_id
                    queue.append((nx, ny))
            group_id += 1

    queue.clear()
    for y in range(h):
        for x in range(w):
            if groups[y][x] >= 0:
                queue.append((x, y))

    while queue:
        cx, cy = queue.popleft()
        gid = groups[cy][cx]
        for nx, ny in ((cx - 1, cy), (cx + 1, cy), (cx, cy - 1), (cx, cy + 1)):
            if nx < 0 or ny < 0 or nx >= w or ny >= h:
                continue
            if terrain[ny][nx] not in {TRANSITION, DOOR}:
                continue
            if groups[ny][nx] >= 0:
                continue
            groups[ny][nx] = gid
            queue.append((nx, ny))

    for y in range(h):
        for x in range(w):
            if terrain[y][x] in {CORRIDOR, TRANSITION, DOOR} and groups[y][x] < 0:
                groups[y][x] = 0
    return groups


def bfs_reachable(
    terrain: list[list[int]],
    start: tuple[int, int],
) -> set[tuple[int, int]]:
    if terrain_at(terrain, start[0], start[1]) == EMPTY:
        return set()
    queue = deque([start])
    visited = {start}
    while queue:
        x, y = queue.popleft()
        for nx, ny in ((x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)):
            if (nx, ny) in visited:
                continue
            if terrain_at(terrain, nx, ny) == EMPTY:
                continue
            visited.add((nx, ny))
            queue.append((nx, ny))
    return visited


def prune_unreachable(
    terrain: list[list[int]],
    rooms: list[RoomRegion],
) -> tuple[list[list[int]], list[RoomRegion]]:
    if not rooms:
        return terrain, []

    start = rooms[0].center
    reachable = bfs_reachable(terrain, start)
    pruned = [row[:] for row in terrain]
    for y in range(len(pruned)):
        for x in range(len(pruned[0])):
            if pruned[y][x] != EMPTY and (x, y) not in reachable:
                pruned[y][x] = EMPTY

    kept_rooms: list[RoomRegion] = []
    for room in rooms:
        filtered = [cell for cell in room.cells if cell in reachable and pruned[cell[1]][cell[0]] != EMPTY]
        if len(filtered) < 8:
            continue
        center = center_of_cells(filtered)
        kept_rooms.append(RoomRegion(cells=tuple(sorted(filtered)), center=center))
    return pruned, kept_rooms


def generate_layout(spec: EpisodeMapSpec, rng: random.Random) -> GeneratedLayout:
    terrain = [[EMPTY for _ in range(GRID_W)] for _ in range(GRID_H)]
    rooms = place_rooms(terrain, rng, spec.room_target)
    if len(rooms) < 6:
        raise ValueError(f"{spec.output_map}: room placement failed to reach usable count.")

    for room_i, room_j in corridor_edges(rooms, rng):
        # Pull corridor widths back to roughly half of the widened pass.
        width = rng.choice((2, 3))
        connect_rooms_with_corridor(terrain, rooms[room_i].center, rooms[room_j].center, width, rng)

    terrain = mark_transition_zones(terrain)
    terrain, rooms = prune_unreachable(terrain, rooms)
    if len(rooms) < 4:
        raise ValueError(f"{spec.output_map}: too few connected rooms after pruning.")
    # Keep spawn in a compact starter room.
    smallest_room_idx = min(range(len(rooms)), key=lambda idx: len(rooms[idx].cells))
    if smallest_room_idx != 0:
        rooms[0], rooms[smallest_room_idx] = rooms[smallest_room_idx], rooms[0]
    door_group_grid = place_doorways(terrain, rng)
    corridor_group_grid = build_corridor_group_grid(terrain)

    room_index_grid = [[-1 for _ in range(GRID_W)] for _ in range(GRID_H)]
    for room_index, room in enumerate(rooms):
        for x, y in room.cells:
            if 0 <= x < GRID_W and 0 <= y < GRID_H and terrain[y][x] == ROOM:
                room_index_grid[y][x] = room_index

    return GeneratedLayout(
        width=GRID_W,
        height=GRID_H,
        terrain=terrain,
        rooms=rooms,
        room_index_grid=room_index_grid,
        door_group_grid=door_group_grid,
        corridor_group_grid=corridor_group_grid,
    )


def grid_to_world(layout: GeneratedLayout, gx: int, gy: int) -> tuple[int, int]:
    x = int(round((gx - (layout.width / 2.0)) * TILE))
    y = int(round(((layout.height / 2.0) - gy) * TILE))
    return x, y


def cell_center_world(layout: GeneratedLayout, cx: int, cy: int) -> tuple[int, int]:
    x = int(round(((cx + 0.5) - (layout.width / 2.0)) * TILE))
    y = int(round(((layout.height / 2.0) - (cy + 0.5)) * TILE))
    return x, y


def add_sector(
    map_data: MutableMap,
    floor_height: int,
    ceiling_height: int,
    floor_texture: str,
    ceiling_texture: str,
    light_level: int,
    special: int = 0,
    tag: int = 0,
) -> int:
    map_data.sectors.append(
        Sector(
            floor_height=floor_height,
            ceiling_height=ceiling_height,
            floor_texture=floor_texture,
            ceiling_texture=ceiling_texture,
            light_level=light_level,
            special=int(special),
            tag=int(tag),
        )
    )
    return len(map_data.sectors) - 1


def add_sidedef(
    map_data: MutableMap,
    sector_idx: int,
    texture_middle: str,
    texture_top: str = "-",
    texture_bottom: str = "-",
    offset_x: int = 0,
    offset_y: int = 0,
    offset_x_top: int | None = None,
    offset_x_bottom: int | None = None,
    offset_x_middle: int | None = None,
    offset_y_top: int | None = None,
    offset_y_bottom: int | None = None,
    offset_y_middle: int | None = None,
) -> int:
    map_data.sidedefs.append(
        Sidedef(
            offset_x=offset_x,
            offset_y=offset_y,
            texture_top=texture_top,
            texture_bottom=texture_bottom,
            texture_middle=texture_middle,
            sector=sector_idx,
            offset_x_top=offset_x_top,
            offset_x_bottom=offset_x_bottom,
            offset_x_middle=offset_x_middle,
            offset_y_top=offset_y_top,
            offset_y_bottom=offset_y_bottom,
            offset_y_middle=offset_y_middle,
        )
    )
    return len(map_data.sidedefs) - 1


def build_axis_profile(
    length: int,
    rng: random.Random,
    min_level: int = -48,
    max_level: int = 48,
) -> list[int]:
    profile = [0 for _ in range(length)]
    level = rng.randrange(min_level, max_level + 1, 8)
    direction = rng.choice((-1, 1))
    step_height = 8
    i = 0
    while i < length:
        run = rng.randint(10, 18)
        flat_run = rng.random() < 0.20
        delta = 0 if flat_run else direction * step_height
        for _ in range(run):
            if i >= length:
                break
            profile[i] = level
            if delta != 0:
                next_level = level + delta
                if next_level < min_level or next_level > max_level:
                    # Keep run direction stable: flatten out instead of immediate reversal.
                    delta = 0
                else:
                    level = next_level
            i += 1
        if delta != 0:
            direction = 1 if delta > 0 else -1
            if rng.random() < 0.35:
                direction *= -1
        elif rng.random() < 0.55:
            direction *= -1
    return profile


def corridor_axis_votes(terrain: list[list[int]], x: int, y: int) -> tuple[int, int]:
    corridor_like = {CORRIDOR, TRANSITION, DOOR}
    horizontal = 1
    vertical = 1
    nx = x - 1
    while terrain_at(terrain, nx, y) in corridor_like:
        horizontal += 1
        nx -= 1
    nx = x + 1
    while terrain_at(terrain, nx, y) in corridor_like:
        horizontal += 1
        nx += 1
    ny = y - 1
    while terrain_at(terrain, x, ny) in corridor_like:
        vertical += 1
        ny -= 1
    ny = y + 1
    while terrain_at(terrain, x, ny) in corridor_like:
        vertical += 1
        ny += 1
    return horizontal, vertical


def build_corridor_axis_grid(layout: GeneratedLayout) -> list[list[str | None]]:
    axis_grid: list[list[str | None]] = [[None for _ in range(layout.width)] for _ in range(layout.height)]
    corridor_like = {CORRIDOR, TRANSITION, DOOR}

    for y in range(layout.height):
        for x in range(layout.width):
            if layout.terrain[y][x] not in corridor_like:
                continue
            h_votes, v_votes = corridor_axis_votes(layout.terrain, x, y)
            if h_votes > v_votes:
                axis_grid[y][x] = "h"
            elif v_votes > h_votes:
                axis_grid[y][x] = "v"

    for _ in range(8):
        changed = False
        for y in range(layout.height):
            for x in range(layout.width):
                if layout.terrain[y][x] not in corridor_like or axis_grid[y][x] is not None:
                    continue
                neighbor_axes: list[str] = []
                for nx, ny in ((x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)):
                    if nx < 0 or ny < 0 or nx >= layout.width or ny >= layout.height:
                        continue
                    neighbor_axis = axis_grid[ny][nx]
                    if neighbor_axis is not None:
                        neighbor_axes.append(neighbor_axis)
                if not neighbor_axes:
                    continue
                h_votes = sum(1 for axis in neighbor_axes if axis == "h")
                v_votes = len(neighbor_axes) - h_votes
                if h_votes > v_votes:
                    axis_grid[y][x] = "h"
                    changed = True
                elif v_votes > h_votes:
                    axis_grid[y][x] = "v"
                    changed = True
        if not changed:
            break

    for y in range(layout.height):
        for x in range(layout.width):
            if layout.terrain[y][x] not in corridor_like or axis_grid[y][x] is not None:
                continue
            inferred = doorway_axis(layout.terrain, x, y)
            if inferred is not None:
                axis_grid[y][x] = inferred
            else:
                h_votes, v_votes = corridor_axis_votes(layout.terrain, x, y)
                axis_grid[y][x] = "h" if h_votes >= v_votes else "v"
    return axis_grid


def enforce_walkable_step_limits(
    layout: GeneratedLayout,
    floors: list[list[int]],
    max_step: int = 8,  # Max walkable is 24
    fixed_cells: set[tuple[int, int]] | None = None,
) -> None:
    walkable = {ROOM, CORRIDOR, TRANSITION, DOOR}
    max_units = max(1, max_step // 8)
    units = [[int(round(floors[y][x] / 8.0)) for x in range(layout.width)] for y in range(layout.height)]
    fixed_set = fixed_cells or set()
    fixed = [
        [
            (layout.terrain[y][x] == ROOM) or ((x, y) in fixed_set)
            for x in range(layout.width)
        ]
        for y in range(layout.height)
    ]

    edges: list[tuple[int, int, int, int]] = []
    for y in range(layout.height):
        for x in range(layout.width):
            if layout.terrain[y][x] not in walkable:
                continue
            if x + 1 < layout.width and layout.terrain[y][x + 1] in walkable:
                edges.append((x, y, x + 1, y))
            if y + 1 < layout.height and layout.terrain[y + 1][x] in walkable:
                edges.append((x, y, x, y + 1))

    def relax_edge(x1: int, y1: int, x2: int, y2: int) -> bool:
        a = units[y1][x1]
        b = units[y2][x2]
        if abs(a - b) <= max_units:
            return False

        if a >= b:
            hx, hy, hv = x1, y1, a
            lx, ly, lv = x2, y2, b
        else:
            hx, hy, hv = x2, y2, b
            lx, ly, lv = x1, y1, a

        high_fixed = fixed[hy][hx]
        low_fixed = fixed[ly][lx]
        changed = False

        if high_fixed and low_fixed:
            return False
        if high_fixed:
            new_low = hv - max_units
            if units[ly][lx] != new_low:
                units[ly][lx] = new_low
                changed = True
        elif low_fixed:
            new_high = lv + max_units
            if units[hy][hx] != new_high:
                units[hy][hx] = new_high
                changed = True
        else:
            excess = hv - lv - max_units
            move_high = (excess + 1) // 2
            move_low = excess // 2
            new_high = hv - move_high
            new_low = lv + move_low
            if units[hy][hx] != new_high:
                units[hy][hx] = new_high
                changed = True
            if units[ly][lx] != new_low:
                units[ly][lx] = new_low
                changed = True
        return changed

    max_iter = 256
    for _ in range(max_iter):
        changed = False
        for x1, y1, x2, y2 in edges:
            if relax_edge(x1, y1, x2, y2):
                changed = True
        for x1, y1, x2, y2 in reversed(edges):
            if relax_edge(x1, y1, x2, y2):
                changed = True
        if not changed:
            break

    for y in range(layout.height):
        for x in range(layout.width):
            if layout.terrain[y][x] in walkable:
                floors[y][x] = units[y][x] * 8


def principal_axis(cells: list[tuple[int, int]]) -> tuple[float, float]:
    if not cells:
        return 1.0, 0.0
    mx = sum(x for x, _y in cells) / len(cells)
    my = sum(y for _x, y in cells) / len(cells)
    xx = 0.0
    yy = 0.0
    xy = 0.0
    for x, y in cells:
        dx = x - mx
        dy = y - my
        xx += dx * dx
        yy += dy * dy
        xy += dx * dy
    if abs(xy) < 1.0e-9 and abs(xx - yy) < 1.0e-9:
        return 1.0, 0.0
    theta = 0.5 * math.atan2(2.0 * xy, xx - yy)
    vx = math.cos(theta)
    vy = math.sin(theta)
    length = math.hypot(vx, vy)
    if length < 1.0e-9:
        return 1.0, 0.0
    return vx / length, vy / length


def build_floor_grid(layout: GeneratedLayout, map_seed: int) -> list[list[int]]:
    rng = random.Random((map_seed ^ 0x9E3779B9) & 0xFFFFFFFF)
    floors = [[0 for _ in range(layout.width)] for _ in range(layout.height)]
    corridor_walkable = {CORRIDOR, TRANSITION, DOOR}

    group_cells: dict[int, list[tuple[int, int]]] = {}
    for y in range(layout.height):
        for x in range(layout.width):
            if layout.terrain[y][x] not in corridor_walkable:
                continue
            group_id = layout.corridor_group_grid[y][x]
            if group_id < 0:
                continue
            group_cells.setdefault(group_id, []).append((x, y))

    for group_id, cells in group_cells.items():
        if not cells:
            continue
        local_rng = random.Random((map_seed * 1315423911 + group_id * 2654435761) & 0xFFFFFFFF)
        vx, vy = principal_axis(cells)
        projections = [((x * vx) + (y * vy)) for x, y in cells]
        min_proj = min(projections)
        max_proj = max(projections)
        span = max_proj - min_proj
        axis_len = max(2, int(math.ceil(span)) + 1)
        profile = build_axis_profile(axis_len, local_rng, min_level=-48, max_level=48)

        if rng.random() < 0.20 and axis_len >= 8:
            start = rng.randint(0, axis_len - 4)
            end = min(axis_len, start + rng.randint(4, 10))
            flat_level = profile[start]
            for i in range(start, end):
                profile[i] = flat_level

        for x, y in cells:
            if span < 1.0e-6:
                idx = axis_len // 2
            else:
                proj = (x * vx) + (y * vy)
                t = (proj - min_proj) / span
                idx = int(round(t * (axis_len - 1)))
            idx = max(0, min(axis_len - 1, idx))
            floors[y][x] = profile[idx]

    landing_fixed: set[tuple[int, int]] = set()
    # First and last 512 map units of each corridor branch are flat at room floor level.
    for group_id, cells in group_cells.items():
        if not cells:
            continue
        cell_set = set(cells)
        anchors: list[tuple[int, int]] = []
        for x, y in cells:
            for nx, ny in ((x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)):
                if nx < 0 or ny < 0 or nx >= layout.width or ny >= layout.height:
                    continue
                if layout.terrain[ny][nx] == ROOM:
                    anchors.append((x, y))
                    break
        if not anchors:
            continue

        distance: dict[tuple[int, int], int] = {}
        queue: deque[tuple[int, int]] = deque()
        for anchor in anchors:
            if anchor in distance:
                continue
            distance[anchor] = 0
            queue.append(anchor)

        while queue:
            x, y = queue.popleft()
            dist = distance[(x, y)]
            if dist + 1 >= CORRIDOR_END_FLAT_CELLS:
                continue
            for nx, ny in ((x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)):
                if (nx, ny) not in cell_set:
                    continue
                next_dist = dist + 1
                prev = distance.get((nx, ny))
                if prev is not None and prev <= next_dist:
                    continue
                distance[(nx, ny)] = next_dist
                queue.append((nx, ny))

        for (x, y), dist in distance.items():
            if dist < CORRIDOR_END_FLAT_CELLS:
                floors[y][x] = 0
                landing_fixed.add((x, y))

    for y in range(layout.height):
        for x in range(layout.width):
            if layout.terrain[y][x] not in corridor_walkable:
                continue
            if (x, y) in landing_fixed:
                continue
            for nx, ny in ((x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)):
                if nx < 0 or ny < 0 or nx >= layout.width or ny >= layout.height:
                    continue
                if layout.terrain[ny][nx] == ROOM:
                    floors[y][x] = max(-24, min(24, floors[y][x]))
                    break

    door_cells_by_group: dict[int, list[tuple[int, int]]] = {}
    for y in range(layout.height):
        for x in range(layout.width):
            if layout.terrain[y][x] != DOOR:
                continue
            group_id = layout.door_group_grid[y][x]
            if group_id < 0:
                continue
            door_cells_by_group.setdefault(group_id, []).append((x, y))

    for cells in door_cells_by_group.values():
        if not cells:
            continue
        avg = sum(floors[y][x] for x, y in cells) / len(cells)
        snapped = int(round(avg / 8.0) * 8)
        for x, y in cells:
            if (x, y) in landing_fixed:
                continue
            floors[y][x] = snapped

    enforce_walkable_step_limits(layout, floors, max_step=24, fixed_cells=landing_fixed)
    return floors


def texture_from_palette(palette: tuple[str, ...], key: int, fallback: str) -> str:
    if not palette:
        return fallback
    return palette[key % len(palette)]


def cell_wall_texture(
    layout: GeneratedLayout,
    theme: ThemeStyle,
    x: int,
    y: int,
    terrain_value: int,
    room_wall_by_index: dict[int, str],
    room_ornament_by_index: dict[int, str],
    corridor_wall_by_group: dict[int, str],
) -> str:
    if terrain_value == ROOM:
        room_index = layout.room_index_grid[y][x] if 0 <= y < layout.height and 0 <= x < layout.width else -1
        if room_index >= 0:
            base = room_wall_by_index.get(room_index, theme.room_wall_textures[0])
            ornament = room_ornament_by_index.get(room_index, base)
            if ornament != base:
                deco_key = (x * 29) + (y * 17) + (room_index * 13)
                if deco_key % 19 == 0:
                    return ornament
            return base
        return theme.room_wall_textures[0]
    if terrain_value == DOOR:
        group_id = layout.corridor_group_grid[y][x] if 0 <= y < layout.height and 0 <= x < layout.width else -1
        if group_id >= 0:
            return corridor_wall_by_group.get(group_id, theme.corridor_wall_textures[0])
        return theme.corridor_wall_textures[0]
    if terrain_value in {CORRIDOR, TRANSITION}:
        group_id = layout.corridor_group_grid[y][x] if 0 <= y < layout.height and 0 <= x < layout.width else -1
        if group_id >= 0:
            return corridor_wall_by_group.get(group_id, theme.corridor_wall_textures[0])
        return theme.corridor_wall_textures[0]
    return theme.room_wall_textures[0]


def add_boundary_line(
    map_data: MutableMap,
    v1_idx: int,
    v2_idx: int,
    right_sector: int,
    left_sector: int,
    right_wall_texture: str,
    left_wall_texture: str | None = None,
) -> int:
    if left_sector < 0:
        right_side = add_sidedef(
            map_data,
            sector_idx=right_sector,
            texture_middle=right_wall_texture,
            texture_top="-",
            texture_bottom="-",
        )
        line = Linedef(
            v1=v1_idx,
            v2=v2_idx,
            flags=0x0001,
            special=0,
            tag=0,
            right=right_side,
            left=-1,
        )
    else:
        if left_sector == right_sector:
            return -1
        left_tex = left_wall_texture or right_wall_texture
        right_side = add_sidedef(
            map_data,
            sector_idx=right_sector,
            texture_middle="-",
            texture_top=right_wall_texture,
            texture_bottom=right_wall_texture,
        )
        left_side = add_sidedef(
            map_data,
            sector_idx=left_sector,
            texture_middle="-",
            texture_top=left_tex,
            texture_bottom=left_tex,
        )
        line = Linedef(
            v1=v1_idx,
            v2=v2_idx,
            flags=0x0004,
            special=0,
            tag=0,
            right=right_side,
            left=left_side,
        )
    map_data.linedefs.append(line)
    return len(map_data.linedefs) - 1


def terrain_to_map(
    layout: GeneratedLayout,
    spec: EpisodeMapSpec,
    theme: ThemeStyle,
) -> tuple[MutableMap, dict[int, set[int]]]:
    map_data = MutableMap(name=spec.output_map)
    floor_grid = build_floor_grid(layout, spec.map_seed)
    sector_cache: dict[object, int] = {}
    sector_grid = [[-1 for _ in range(layout.width)] for _ in range(layout.height)]
    door_lines_by_sector: dict[int, set[int]] = {}

    for y in range(layout.height):
        for x in range(layout.width):
            terrain_value = layout.terrain[y][x]
            if terrain_value == EMPTY:
                continue
            floor_height = floor_grid[y][x]
            if terrain_value == DOOR:
                group_id = layout.door_group_grid[y][x]
                sector_key = ("door", group_id if group_id >= 0 else (x, y))
            else:
                sector_key = (terrain_value, floor_height)
            if sector_key not in sector_cache:
                if terrain_value == ROOM:
                    floor_tex = theme.room_floor
                    light = theme.room_light
                    ceiling_height = floor_height + 128
                elif terrain_value in {CORRIDOR, TRANSITION}:
                    floor_tex = theme.corridor_floor
                    light = theme.corridor_light
                    ceiling_height = floor_height + 128
                elif terrain_value == DOOR:
                    floor_tex = theme.corridor_floor
                    light = theme.corridor_light
                    ceiling_height = floor_height + 4
                else:
                    floor_tex = theme.transition_floor
                    light = theme.transition_light
                    ceiling_height = floor_height + 120
                if terrain_value != DOOR and ceiling_height - floor_height < 96:
                    ceiling_height = floor_height + 96
                sector_cache[sector_key] = add_sector(
                    map_data,
                    floor_height=floor_height,
                    ceiling_height=ceiling_height,
                    floor_texture=floor_tex,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=light,
                )
            sector_grid[y][x] = sector_cache[sector_key]

    room_wall_by_index: dict[int, str] = {}
    room_ornament_by_index: dict[int, str] = {}
    for room_index in range(len(layout.rooms)):
        texture_key = spec.map_seed + (room_index * 7)
        base_texture = texture_from_palette(
            theme.room_wall_textures,
            texture_key,
            theme.room_wall_textures[0],
        )
        room_wall_by_index[room_index] = base_texture
        accent_options = [tex for tex in theme.room_wall_textures if tex != base_texture]
        if accent_options:
            room_ornament_by_index[room_index] = accent_options[(texture_key // 3) % len(accent_options)]
        else:
            room_ornament_by_index[room_index] = base_texture
    corridor_wall_by_group: dict[int, str] = {}
    seen_groups: set[int] = set()
    for y in range(layout.height):
        for x in range(layout.width):
            if layout.terrain[y][x] not in {CORRIDOR, TRANSITION, DOOR}:
                continue
            group_id = layout.corridor_group_grid[y][x]
            if group_id < 0 or group_id in seen_groups:
                continue
            seen_groups.add(group_id)
            texture_key = spec.map_seed + (group_id * 17)
            corridor_wall_by_group[group_id] = texture_from_palette(
                theme.corridor_wall_textures,
                texture_key,
                theme.corridor_wall_textures[0],
            )

    vertex_lookup: dict[tuple[int, int], int] = {}

    def vertex_index(grid_point: tuple[int, int]) -> int:
        if grid_point in vertex_lookup:
            return vertex_lookup[grid_point]
        wx, wy = grid_to_world(layout, grid_point[0], grid_point[1])
        map_data.vertices.append(Vertex(wx, wy))
        idx = len(map_data.vertices) - 1
        vertex_lookup[grid_point] = idx
        return idx

    edge_seen: set[tuple[tuple[int, int], tuple[int, int]]] = set()

    def edge_key(a: tuple[int, int], b: tuple[int, int]) -> tuple[tuple[int, int], tuple[int, int]]:
        return (a, b) if a <= b else (b, a)

    side_defs = (
        (0, -1, lambda x, y: ((x, y), (x + 1, y))),        # north
        (0, 1, lambda x, y: ((x + 1, y + 1), (x, y + 1))), # south
        (-1, 0, lambda x, y: ((x, y + 1), (x, y))),        # west
        (1, 0, lambda x, y: ((x + 1, y), (x + 1, y + 1))), # east
    )

    for y in range(layout.height):
        for x in range(layout.width):
            current = layout.terrain[y][x]
            if current == EMPTY:
                continue
            right_sector = sector_grid[y][x]
            for dx, dy, point_builder in side_defs:
                neighbor = terrain_at(layout.terrain, x + dx, y + dy)
                neighbor_sector = sector_grid[y + dy][x + dx] if 0 <= (x + dx) < layout.width and 0 <= (y + dy) < layout.height else -1
                if neighbor_sector == right_sector:
                    continue
                p1, p2 = point_builder(x, y)
                key = edge_key(p1, p2)
                if key in edge_seen:
                    continue
                edge_seen.add(key)

                v1 = vertex_index(p1)
                v2 = vertex_index(p2)
                left_sector = neighbor_sector
                right_texture = cell_wall_texture(
                    layout=layout,
                    theme=theme,
                    x=x,
                    y=y,
                    terrain_value=current,
                    room_wall_by_index=room_wall_by_index,
                    room_ornament_by_index=room_ornament_by_index,
                    corridor_wall_by_group=corridor_wall_by_group,
                )
                left_texture = None
                if neighbor != EMPTY and left_sector >= 0:
                    left_texture = cell_wall_texture(
                        layout=layout,
                        theme=theme,
                        x=x + dx,
                        y=y + dy,
                        terrain_value=neighbor,
                        room_wall_by_index=room_wall_by_index,
                        room_ornament_by_index=room_ornament_by_index,
                        corridor_wall_by_group=corridor_wall_by_group,
                    )
                if (
                    (current == DOOR and neighbor in {ROOM, CORRIDOR, TRANSITION})
                    or (neighbor == DOOR and current in {ROOM, CORRIDOR, TRANSITION})
                ):
                    right_texture = theme.door_texture
                    if neighbor != EMPTY and left_sector >= 0:
                        left_texture = theme.door_texture
                line_idx = add_boundary_line(
                    map_data,
                    v1_idx=v1,
                    v2_idx=v2,
                    right_sector=right_sector,
                    left_sector=left_sector,
                    right_wall_texture=right_texture,
                    left_wall_texture=left_texture,
                )
                if line_idx < 0:
                    continue
                if current == DOOR and neighbor in {ROOM, CORRIDOR, TRANSITION}:
                    door_lines_by_sector.setdefault(right_sector, set()).add(line_idx)
                elif neighbor == DOOR and current in {ROOM, CORRIDOR, TRANSITION} and left_sector >= 0:
                    door_lines_by_sector.setdefault(left_sector, set()).add(line_idx)

    return map_data, door_lines_by_sector


def rotate_offset(dx: int, dy: int, angle: int) -> tuple[int, int]:
    radians = math.radians(angle % 360)
    x = round(dx * math.cos(radians) - dy * math.sin(radians))
    y = round(dx * math.sin(radians) + dy * math.cos(radians))
    return int(x), int(y)


def add_object(
    map_data: MutableMap,
    x: int,
    y: int,
    thing_type: int,
    angle: int = 0,
    flags: int = THING_FLAG_EASY | THING_FLAG_MEDIUM | THING_FLAG_HARD,
    *,
    line_segments: list[tuple[tuple[float, float], tuple[float, float]]] | None = None,
    min_spacing_units: float = OBJECT_MIN_SPACING_UNITS,
    place_on_walkable_spot: bool = False,
    walkable_platform_polys: list[tuple[tuple[float, float], ...]] | None = None,
    non_walkable_polys: list[tuple[tuple[float, float], ...]] | None = None,
    debug_label: str | None = None,
) -> bool:
    px = float(x)
    py = float(y)
    spacing_sq = float(min_spacing_units) * float(min_spacing_units)
    label = debug_label or f"type={thing_type}"
    monster_radius = monster_collision_radius_units(thing_type)
    monster_line_clearance_sq = (
        float(MONSTER_BOX_LINE_CLEARANCE_UNITS) * float(MONSTER_BOX_LINE_CLEARANCE_UNITS)
        if monster_radius is not None
        else 0.0
    )

    if line_segments is not None:
        for a, b in line_segments:
            if point_to_segment_distance_sq((px, py), a, b) < spacing_sq:
                log_trace(
                    f"OBJECT_REJECT label={label} reason=line_clearance x={x} y={y} spacing={min_spacing_units:.1f}"
                )
                return False
            if monster_radius is not None and monster_line_clearance_sq > 0.0:
                half = float(monster_radius)
                edge_dist_sq = segment_to_aabb_distance_sq(
                    a,
                    b,
                    px - half,
                    px + half,
                    py - half,
                    py + half,
                )
                if edge_dist_sq < monster_line_clearance_sq:
                    log_trace(
                        f"OBJECT_REJECT label={label} reason=monster_box_line_clearance "
                        f"x={x} y={y} radius={monster_radius:.1f} clearance={MONSTER_BOX_LINE_CLEARANCE_UNITS:.1f}"
                    )
                    return False

    for existing in map_data.things:
        dx = px - float(existing.x)
        dy = py - float(existing.y)
        if (dx * dx) + (dy * dy) < spacing_sq:
            log_trace(
                f"OBJECT_REJECT label={label} reason=thing_spacing x={x} y={y} "
                f"other_type={existing.thing_type} other_x={existing.x} other_y={existing.y}"
            )
            return False

    blocked = non_walkable_polys or []
    if blocked and any(point_in_polygon((px, py), poly) for poly in blocked):
        log_trace(f"OBJECT_REJECT label={label} reason=non_walkable_poly x={x} y={y}")
        return False

    walkable = walkable_platform_polys or []
    if place_on_walkable_spot:
        if not walkable:
            log_trace(f"OBJECT_REJECT label={label} reason=no_walkable_pool x={x} y={y}")
            return False
        in_walkable = any(point_in_polygon((px, py), poly) for poly in walkable)
        if not in_walkable:
            log_trace(f"OBJECT_REJECT label={label} reason=outside_walkable_poly x={x} y={y}")
            return False

    map_data.things.append(
        Thing(
            x=int(x),
            y=int(y),
            angle=int(angle % 360),
            thing_type=int(thing_type),
            flags=int(flags),
        )
    )
    log_trace(f"OBJECT_PLACE label={label} type={thing_type} x={x} y={y} angle={angle % 360} flags={flags}")
    return True


def collect_line_segments(
    map_data: MutableMap,
    *,
    edge_only: bool = False,
) -> list[tuple[tuple[float, float], tuple[float, float]]]:
    def line_is_edge(line: Linedef) -> bool:
        if line.left < 0 or line.right < 0:
            return True
        if line.left >= len(map_data.sidedefs) or line.right >= len(map_data.sidedefs):
            return True
        left_sector = map_data.sidedefs[line.left].sector
        right_sector = map_data.sidedefs[line.right].sector
        if left_sector < 0 or right_sector < 0:
            return True
        if left_sector >= len(map_data.sectors) or right_sector >= len(map_data.sectors):
            return True
        left = map_data.sectors[left_sector]
        right = map_data.sectors[right_sector]
        return (left.floor_height != right.floor_height) or (left.ceiling_height != right.ceiling_height)

    segments: list[tuple[tuple[float, float], tuple[float, float]]] = []
    for line in map_data.linedefs:
        if edge_only and not line_is_edge(line):
            continue
        if line.v1 < 0 or line.v2 < 0 or line.v1 >= len(map_data.vertices) or line.v2 >= len(map_data.vertices):
            continue
        v1 = map_data.vertices[line.v1]
        v2 = map_data.vertices[line.v2]
        segments.append(((float(v1.x), float(v1.y)), (float(v2.x), float(v2.y))))
    return segments


def point_clear_of_lines(
    point: tuple[float, float],
    line_segments: list[tuple[tuple[float, float], tuple[float, float]]],
    min_spacing_units: float,
) -> bool:
    min_sq = float(min_spacing_units) * float(min_spacing_units)
    for a, b in line_segments:
        if point_to_segment_distance_sq(point, a, b) < min_sq:
            return False
    return True


def populate_things(
    map_data: MutableMap,
    layout: GeneratedLayout,
    spec: EpisodeMapSpec,
    rng: random.Random,
) -> tuple[int, int]:
    # Legacy grid-layout population path removed; poly pipeline is authoritative.
    raise RuntimeError("populate_things() legacy path is retired; use populate_things_poly()/add_map_objects().")


def line_midpoint(map_data: MutableMap, line_idx: int) -> tuple[float, float]:
    line = map_data.linedefs[line_idx]
    v1 = map_data.vertices[line.v1]
    v2 = map_data.vertices[line.v2]
    return ((v1.x + v2.x) / 2.0, (v1.y + v2.y) / 2.0)


def line_length_sq(map_data: MutableMap, line_idx: int) -> int:
    line = map_data.linedefs[line_idx]
    v1 = map_data.vertices[line.v1]
    v2 = map_data.vertices[line.v2]
    dx = v2.x - v1.x
    dy = v2.y - v1.y
    return dx * dx + dy * dy


def split_linedef_near_vertex(
    map_data: MutableMap,
    line_idx: int,
    near_vertex_idx: int,
    segment_len: float = 4.0,
) -> int:
    if line_idx < 0 or line_idx >= len(map_data.linedefs):
        return line_idx
    line = map_data.linedefs[line_idx]
    if near_vertex_idx not in {line.v1, line.v2}:
        return line_idx

    v_near = map_data.vertices[near_vertex_idx]
    far_idx = line.v2 if line.v1 == near_vertex_idx else line.v1
    v_far = map_data.vertices[far_idx]
    dx = float(v_far.x - v_near.x)
    dy = float(v_far.y - v_near.y)
    length = math.hypot(dx, dy)
    if length <= (segment_len + 0.5):
        return line_idx

    t = max(0.0, min(1.0, segment_len / max(length, 1.0e-6)))
    cut_x = int(round(v_near.x + dx * t))
    cut_y = int(round(v_near.y + dy * t))
    if (cut_x, cut_y) in {(v_near.x, v_near.y), (v_far.x, v_far.y)}:
        return line_idx

    map_data.vertices.append(Vertex(cut_x, cut_y))
    cut_idx = len(map_data.vertices) - 1

    if line.v1 == near_vertex_idx:
        line.v1 = cut_idx
        # Preserve original winding: near -> cut.
        seg = Linedef(near_vertex_idx, cut_idx, line.flags, 0, 0, line.right, line.left)
    else:
        line.v2 = cut_idx
        # Preserve original winding: cut -> near.
        seg = Linedef(cut_idx, near_vertex_idx, line.flags, 0, 0, line.right, line.left)

    map_data.linedefs.append(seg)
    return len(map_data.linedefs) - 1


def clone_sidedef(map_data: MutableMap, sidedef_idx: int) -> int:
    if sidedef_idx < 0 or sidedef_idx >= len(map_data.sidedefs):
        return sidedef_idx
    base = map_data.sidedefs[sidedef_idx]
    map_data.sidedefs.append(
        Sidedef(
            offset_x=base.offset_x,
            offset_y=base.offset_y,
            texture_top=base.texture_top,
            texture_bottom=base.texture_bottom,
            texture_middle=base.texture_middle,
            sector=base.sector,
            offset_x_top=base.offset_x_top,
            offset_x_bottom=base.offset_x_bottom,
            offset_x_middle=base.offset_x_middle,
            offset_y_top=base.offset_y_top,
            offset_y_bottom=base.offset_y_bottom,
            offset_y_middle=base.offset_y_middle,
        )
    )
    return len(map_data.sidedefs) - 1


def assign_door_actions(
    map_data: MutableMap,
    door_lines_by_sector: dict[int, set[int]],
    door_texture: str,
    locked_door_colors: dict[int, str] | None = None,
) -> None:
    locked = locked_door_colors or {}
    door_sectors = set(door_lines_by_sector.keys())

    # Keep thin one-sided door-frame/jamb walls visually stable as the door sector moves.
    for line in map_data.linedefs:
        if line.left >= 0 or line.right < 0:
            continue
        side = map_data.sidedefs[line.right]
        if side.sector not in door_sectors:
            continue
        line.flags &= ~0x0008
        line.flags |= 0x0010

    for door_sector, line_indices in door_lines_by_sector.items():
        lock_color = locked.get(door_sector, "")
        door_special = DOOM_DOOR_SPECIAL_BY_COLOR.get(lock_color, DOOM_NONKEY_DOOR_SPECIAL)
        face_clusters: dict[tuple[int, str, int], list[tuple[int, int]]] = {}
        for line_idx in sorted(line_indices):
            line = map_data.linedefs[line_idx]
            if line.left < 0 or line.right < 0:
                continue
            right_sector = map_data.sidedefs[line.right].sector
            left_sector = map_data.sidedefs[line.left].sector
            if right_sector == door_sector and left_sector != door_sector:
                line.v1, line.v2 = line.v2, line.v1
                line.right, line.left = line.left, line.right
                right_sector, left_sector = left_sector, right_sector
            if door_sector not in {right_sector, left_sector}:
                continue
            # Doom namespace DR door specials: repeatable use-open/wait/close.
            line.special = door_special
            line.tag = 0
            line.arg0 = 0
            line.arg1 = 0
            line.arg2 = 0
            line.arg3 = 0
            line.arg4 = 0
            line.flags |= 0x0004
            # Keep DOORTRAK guide surfaces stationary; only moving door-face
            # textures should use lower-pegged scrolling behavior.
            line_has_track = False
            for side_idx in (line.right, line.left):
                if side_idx < 0:
                    continue
                side = map_data.sidedefs[side_idx]
                if DOOR_TRACK_TEXTURE in {side.texture_top, side.texture_middle, side.texture_bottom}:
                    line_has_track = True
                    break
            right_side = map_data.sidedefs[line.right] if line.right >= 0 else None
            left_side = map_data.sidedefs[line.left] if line.left >= 0 else None
            micro_track_boundary = (
                right_side is not None
                and left_side is not None
                and right_side.texture_middle == DOOR_TRACK_TEXTURE
                and right_side.texture_top == "-"
                and right_side.texture_bottom == "-"
                and left_side.texture_middle == DOOR_TRACK_TEXTURE
                and left_side.texture_top == "-"
                and left_side.texture_bottom == "-"
            )
            if micro_track_boundary:
                line.flags &= ~0x0008
                line.flags |= 0x0010
            elif line_has_track:
                line.flags |= 0x0008
                line.flags &= ~0x0010
            else:
                line.flags &= ~0x0008
                line.flags |= 0x0010

            other_sector = left_sector if right_sector == door_sector else right_sector
            v1 = map_data.vertices[line.v1]
            v2 = map_data.vertices[line.v2]
            dx = v2.x - v1.x
            dy = v2.y - v1.y
            if abs(dx) >= abs(dy):
                axis = "h"
                fixed_coord = int(round((v1.y + v2.y) / 2.0))
                along = min(v1.x, v2.x)
            else:
                axis = "v"
                fixed_coord = int(round((v1.x + v2.x) / 2.0))
                along = min(v1.y, v2.y)
            face_clusters.setdefault((other_sector, axis, fixed_coord), []).append((line_idx, along))

        for entries in face_clusters.values():
            if not entries:
                continue
            entries.sort(key=lambda item: item[1])
            base_along = entries[0][1]
            for line_idx, along in entries:
                offset = int(along - base_along)
                line = map_data.linedefs[line_idx]
                for side_idx in (line.right, line.left):
                    if side_idx < 0:
                        continue
                    side = map_data.sidedefs[side_idx]
                    if door_texture in {side.texture_top, side.texture_bottom, side.texture_middle}:
                        side.offset_x = offset
                        side.offset_y = 0

        if lock_color:
            marker_tex = LOCK_FRAME_TEXTURE_BY_COLOR.get(lock_color)
            if marker_tex:
                adjacent_gap_sectors: set[int] = set()
                door_axis = "h"
                longest_door_face = -1.0
                for line_idx in line_indices:
                    line = map_data.linedefs[line_idx]
                    if line.left < 0 or line.right < 0:
                        continue
                    right_sector = map_data.sidedefs[line.right].sector
                    left_sector = map_data.sidedefs[line.left].sector
                    if right_sector == door_sector and left_sector != door_sector:
                        adjacent_gap_sectors.add(left_sector)
                    elif left_sector == door_sector and right_sector != door_sector:
                        adjacent_gap_sectors.add(right_sector)
                    if not (0 <= line.v1 < len(map_data.vertices) and 0 <= line.v2 < len(map_data.vertices)):
                        continue
                    v1 = map_data.vertices[line.v1]
                    v2 = map_data.vertices[line.v2]
                    dx = float(v2.x - v1.x)
                    dy = float(v2.y - v1.y)
                    seg_len = math.hypot(dx, dy)
                    if seg_len > longest_door_face:
                        longest_door_face = seg_len
                        door_axis = "h" if abs(dx) >= abs(dy) else "v"

                for gap_sector in sorted(adjacent_gap_sectors):
                    side_entries: list[tuple[int, int, bool, str, float, int]] = []
                    base_tex = ""

                    for idx, line in enumerate(map_data.linedefs):
                        if not (0 <= line.v1 < len(map_data.vertices) and 0 <= line.v2 < len(map_data.vertices)):
                            continue
                        side_idx = -1
                        other_side_idx = -1
                        if line.right >= 0 and map_data.sidedefs[line.right].sector == gap_sector:
                            side_idx = int(line.right)
                            other_side_idx = int(line.left)
                        elif line.left >= 0 and map_data.sidedefs[line.left].sector == gap_sector:
                            side_idx = int(line.left)
                            other_side_idx = int(line.right)
                        if side_idx < 0:
                            continue

                        v1 = map_data.vertices[line.v1]
                        v2 = map_data.vertices[line.v2]
                        dx = float(v2.x - v1.x)
                        dy = float(v2.y - v1.y)
                        axis = "h" if abs(dx) >= abs(dy) else "v"
                        seg_len = math.hypot(dx, dy)
                        one_sided = line.left < 0 or line.right < 0

                        other_sector = -1
                        if 0 <= other_side_idx < len(map_data.sidedefs):
                            other_sector = int(map_data.sidedefs[other_side_idx].sector)
                        side_entries.append((idx, side_idx, one_sided, axis, seg_len, other_sector))

                        if (
                            not base_tex
                            and 0 <= other_side_idx < len(map_data.sidedefs)
                            and other_sector >= 0
                            and other_sector != door_sector
                            and other_sector not in adjacent_gap_sectors
                        ):
                            other_side = map_data.sidedefs[other_side_idx]
                            for tex in (other_side.texture_middle, other_side.texture_top, other_side.texture_bottom):
                                if tex != "-" and tex != marker_tex and tex != DOOR_TRACK_TEXTURE:
                                    base_tex = tex
                                    break

                    if not side_entries:
                        continue

                    if not base_tex:
                        probe_side = map_data.sidedefs[side_entries[0][1]]
                        for tex in (probe_side.texture_middle, probe_side.texture_top, probe_side.texture_bottom):
                            if tex != "-" and tex != marker_tex and tex != DOOR_TRACK_TEXTURE:
                                base_tex = tex
                                break
                    if not base_tex:
                        base_tex = "STARTAN3"

                    target_entry = max(
                        (entry for entry in side_entries if entry[2] and entry[3] == door_axis),
                        key=lambda entry: entry[4],
                        default=None,
                    )
                    if target_entry is None:
                        target_entry = max(
                            (entry for entry in side_entries if entry[2]),
                            key=lambda entry: entry[4],
                            default=None,
                        )
                    if target_entry is None:
                        continue
                    target_side_idx = int(target_entry[1])

                    for idx, side_idx, one_sided, _axis, _seg_len, _other_sector in side_entries:
                        line = map_data.linedefs[idx]
                        side = map_data.sidedefs[side_idx]
                        if side_idx == target_side_idx:
                            # Marker only on the single back-wall line parallel to the door.
                            side.texture_top = "-"
                            side.texture_middle = marker_tex
                            side.texture_bottom = "-"
                            side.offset_y = 0
                            line.flags &= ~0x0008
                            line.flags |= 0x0010
                            continue

                        if one_sided:
                            side.texture_top = "-"
                            side.texture_middle = base_tex
                            side.texture_bottom = "-"
                            side.offset_y = 0
                        else:
                            side.texture_top = base_tex
                            side.texture_middle = "-"
                            side.texture_bottom = base_tex

                # Final marker-strip cleanup:
                # Keep exactly one one-sided marker line per jamb strip sector.
                # Target the strip line that shares a slab-face vertex so color
                # appears only on the intended room/corridor-facing strip.
                door_vertex_indices: set[int] = set()
                for line_idx in line_indices:
                    if not (0 <= line_idx < len(map_data.linedefs)):
                        continue
                    line = map_data.linedefs[line_idx]
                    if 0 <= line.v1 < len(map_data.vertices):
                        door_vertex_indices.add(int(line.v1))
                    if 0 <= line.v2 < len(map_data.vertices):
                        door_vertex_indices.add(int(line.v2))

                def infer_strip_base_texture(strip_sector: int) -> str:
                    # Prefer neighboring wall texture; fall back to current side.
                    for idx, line in enumerate(map_data.linedefs):
                        if not (0 <= line.v1 < len(map_data.vertices) and 0 <= line.v2 < len(map_data.vertices)):
                            continue
                        side_idx = -1
                        other_idx = -1
                        if line.right >= 0 and map_data.sidedefs[line.right].sector == strip_sector:
                            side_idx = int(line.right)
                            other_idx = int(line.left)
                        elif line.left >= 0 and map_data.sidedefs[line.left].sector == strip_sector:
                            side_idx = int(line.left)
                            other_idx = int(line.right)
                        if side_idx < 0:
                            continue

                        if 0 <= other_idx < len(map_data.sidedefs):
                            other_side = map_data.sidedefs[other_idx]
                            for tex in (other_side.texture_middle, other_side.texture_top, other_side.texture_bottom):
                                if tex != "-" and tex != marker_tex and tex != DOOR_TRACK_TEXTURE:
                                    return tex

                        this_side = map_data.sidedefs[side_idx]
                        for tex in (this_side.texture_middle, this_side.texture_top, this_side.texture_bottom):
                            if tex != "-" and tex != marker_tex and tex != DOOR_TRACK_TEXTURE:
                                return tex
                    return "STARTAN3"

                target_line_by_sector: dict[int, tuple[int, int, float]] = {}
                for idx, line in enumerate(map_data.linedefs):
                    if not (0 <= line.v1 < len(map_data.vertices) and 0 <= line.v2 < len(map_data.vertices)):
                        continue
                    if not (line.left < 0 <= line.right or line.right < 0 <= line.left):
                        continue
                    if line.right >= 0 and line.left < 0:
                        side_idx = int(line.right)
                    elif line.left >= 0 and line.right < 0:
                        side_idx = int(line.left)
                    else:
                        continue
                    if not (0 <= side_idx < len(map_data.sidedefs)):
                        continue
                    sec_idx = int(map_data.sidedefs[side_idx].sector)
                    if sec_idx == door_sector:
                        continue
                    shares_door_vertex = (int(line.v1) in door_vertex_indices) or (int(line.v2) in door_vertex_indices)
                    if not shares_door_vertex:
                        continue

                    v1 = map_data.vertices[line.v1]
                    v2 = map_data.vertices[line.v2]
                    dx = float(v2.x - v1.x)
                    dy = float(v2.y - v1.y)
                    axis = "h" if abs(dx) >= abs(dy) else "v"
                    if axis != door_axis:
                        continue
                    seg_len = math.hypot(dx, dy)

                    existing = target_line_by_sector.get(sec_idx)
                    if existing is None or seg_len > existing[2]:
                        target_line_by_sector[sec_idx] = (idx, side_idx, seg_len)

                if target_line_by_sector:
                    base_tex_by_sector = {
                        sec_idx: infer_strip_base_texture(sec_idx) for sec_idx in target_line_by_sector.keys()
                    }
                    for idx, line in enumerate(map_data.linedefs):
                        if not (line.left < 0 <= line.right or line.right < 0 <= line.left):
                            continue
                        if line.right >= 0 and line.left < 0:
                            side_idx = int(line.right)
                        elif line.left >= 0 and line.right < 0:
                            side_idx = int(line.left)
                        else:
                            continue
                        if not (0 <= side_idx < len(map_data.sidedefs)):
                            continue
                        sec_idx = int(map_data.sidedefs[side_idx].sector)
                        target = target_line_by_sector.get(sec_idx)
                        if target is None:
                            continue
                        side = map_data.sidedefs[side_idx]
                        if idx == target[0]:
                            if side.texture_top != "-" or side.texture_middle != marker_tex or side.texture_bottom != "-":
                                side.texture_top = "-"
                                side.texture_middle = marker_tex
                                side.texture_bottom = "-"
                                side.offset_y = 0
                            line.flags &= ~0x0008
                            line.flags |= 0x0010
                            continue
                        if marker_tex in {side.texture_top, side.texture_middle, side.texture_bottom}:
                            side.texture_top = "-"
                            side.texture_middle = base_tex_by_sector.get(sec_idx, "STARTAN3")
                            side.texture_bottom = "-"
                            side.offset_y = 0

        # Intentionally do not auto-convert nearby short lines to DOORTRAK here.
        # We want side-gap geometry beside the 128-wide slab to remain visible.


def split_one_sided_line_for_center_panel(
    map_data: MutableMap,
    line_idx: int,
    panel_width: float = 64.0,
) -> int:
    if line_idx < 0 or line_idx >= len(map_data.linedefs):
        return line_idx
    line = map_data.linedefs[line_idx]
    if not ((line.left < 0 and line.right >= 0) or (line.right < 0 and line.left >= 0)):
        return line_idx

    if line.right < 0 <= line.left:
        line.v1, line.v2 = line.v2, line.v1
        line.right, line.left = line.left, -1

    if line.right < 0 or line.left >= 0:
        return line_idx

    v1 = map_data.vertices[line.v1]
    v2 = map_data.vertices[line.v2]
    dx = v2.x - v1.x
    dy = v2.y - v1.y
    length = math.hypot(dx, dy)
    if length < (panel_width + 32.0):
        return line_idx

    ux = dx / length
    uy = dy / length
    start_d = (length - panel_width) * 0.5
    end_d = start_d + panel_width

    va = Vertex(int(round(v1.x + ux * start_d)), int(round(v1.y + uy * start_d)))
    vb = Vertex(int(round(v1.x + ux * end_d)), int(round(v1.y + uy * end_d)))
    map_data.vertices.append(va)
    va_idx = len(map_data.vertices) - 1
    map_data.vertices.append(vb)
    vb_idx = len(map_data.vertices) - 1

    original_v2 = line.v2
    line.special = 0
    line.tag = 0
    line.v2 = va_idx

    base_side = map_data.sidedefs[line.right]
    start_shift = int(round(start_d))
    end_shift = int(round(end_d))

    def shifted(value: int | None, delta: int) -> int | None:
        if value is None:
            return None
        return int(value + delta)

    switch_side_idx = add_sidedef(
        map_data,
        sector_idx=base_side.sector,
        texture_middle=base_side.texture_middle,
        texture_top=base_side.texture_top,
        texture_bottom=base_side.texture_bottom,
        offset_x=int(base_side.offset_x + start_shift),
        offset_y=base_side.offset_y,
        offset_x_top=shifted(base_side.offset_x_top, start_shift),
        offset_x_bottom=shifted(base_side.offset_x_bottom, start_shift),
        offset_x_middle=shifted(base_side.offset_x_middle, start_shift),
        offset_y_top=base_side.offset_y_top,
        offset_y_bottom=base_side.offset_y_bottom,
        offset_y_middle=base_side.offset_y_middle,
    )
    tail_side_idx = add_sidedef(
        map_data,
        sector_idx=base_side.sector,
        texture_middle=base_side.texture_middle,
        texture_top=base_side.texture_top,
        texture_bottom=base_side.texture_bottom,
        offset_x=int(base_side.offset_x + end_shift),
        offset_y=base_side.offset_y,
        offset_x_top=shifted(base_side.offset_x_top, end_shift),
        offset_x_bottom=shifted(base_side.offset_x_bottom, end_shift),
        offset_x_middle=shifted(base_side.offset_x_middle, end_shift),
        offset_y_top=base_side.offset_y_top,
        offset_y_bottom=base_side.offset_y_bottom,
        offset_y_middle=base_side.offset_y_middle,
    )

    middle = Linedef(
        v1=va_idx,
        v2=vb_idx,
        flags=line.flags,
        special=0,
        tag=0,
        right=switch_side_idx,
        left=-1,
    )
    map_data.linedefs.append(middle)
    middle_idx = len(map_data.linedefs) - 1

    tail = Linedef(
        v1=vb_idx,
        v2=original_v2,
        flags=line.flags,
        special=0,
        tag=0,
        right=tail_side_idx,
        left=-1,
    )
    map_data.linedefs.append(tail)
    return middle_idx


def set_exit_line_special(line: Linedef) -> None:
    # Doom namespace S1 exit switch.
    line.special = 11
    line.tag = 0
    line.arg0 = 0
    line.arg1 = 0
    line.arg2 = 0
    line.arg3 = 0
    line.arg4 = 0


def build_panel_alcove_on_line(
    map_data: MutableMap,
    panel_line_idx: int,
    panel_texture: str,
    *,
    opening_blocked: bool,
) -> tuple[int, int, Sector, tuple[float, float], tuple[float, float], tuple[float, float]] | None:
    if panel_line_idx < 0 or panel_line_idx >= len(map_data.linedefs):
        return None
    line = map_data.linedefs[panel_line_idx]

    if line.right < 0 <= line.left:
        line.v1, line.v2 = line.v2, line.v1
        line.right, line.left = line.left, -1
    if line.right < 0 or line.left >= 0:
        return None

    room_side = map_data.sidedefs[line.right]
    room_sector_idx = room_side.sector
    if room_sector_idx < 0 or room_sector_idx >= len(map_data.sectors):
        return None
    room_sector = map_data.sectors[room_sector_idx]

    v1 = map_data.vertices[line.v1]
    v2 = map_data.vertices[line.v2]
    dx = float(v2.x - v1.x)
    dy = float(v2.y - v1.y)
    seg_len = math.hypot(dx, dy)
    if seg_len < 1.0:
        return None

    tangent = (dx / seg_len, dy / seg_len)
    room_normal = (dy / seg_len, -dx / seg_len)
    outward = (-room_normal[0], -room_normal[1])
    depth = float(START_ENTRY_ALCOVE_DEPTH_UNITS)
    p3 = Vertex(
        int(round(v2.x + outward[0] * depth)),
        int(round(v2.y + outward[1] * depth)),
    )
    p4 = Vertex(
        int(round(v1.x + outward[0] * depth)),
        int(round(v1.y + outward[1] * depth)),
    )
    map_data.vertices.append(p3)
    p3_idx = len(map_data.vertices) - 1
    map_data.vertices.append(p4)
    p4_idx = len(map_data.vertices) - 1

    alcove_floor = room_sector.floor_height
    alcove_ceiling = min(room_sector.ceiling_height, alcove_floor + START_ENTRY_DOOR_HEIGHT_UNITS)
    if alcove_ceiling <= alcove_floor + 8:
        return None
    alcove_sector = add_sector(
        map_data,
        floor_height=alcove_floor,
        ceiling_height=alcove_ceiling,
        floor_texture=room_sector.floor_texture,
        ceiling_texture=room_sector.ceiling_texture,
        light_level=max(96, room_sector.light_level - 8),
    )

    frame_tex = room_side.texture_middle if room_side.texture_middle != "-" else DOOR_TRACK_TEXTURE
    room_side.texture_middle = "-"
    room_side.texture_top = frame_tex
    room_side.texture_bottom = "-"

    alcove_front_side = add_sidedef(
        map_data,
        sector_idx=alcove_sector,
        texture_middle="-",
        texture_top=frame_tex,
        texture_bottom="-",
        offset_x=room_side.offset_x,
        offset_y=room_side.offset_y,
        offset_x_top=room_side.offset_x_top,
        offset_x_bottom=room_side.offset_x_bottom,
        offset_x_middle=room_side.offset_x_middle,
        offset_y_top=room_side.offset_y_top,
        offset_y_bottom=room_side.offset_y_bottom,
        offset_y_middle=room_side.offset_y_middle,
    )
    line.left = alcove_front_side
    line.flags |= 0x0004  # twosided
    if opening_blocked:
        line.flags |= 0x0001
    else:
        line.flags &= ~0x0001
    line.flags |= 0x0008  # upper unpegged: keep top texture anchored at ceiling.
    line.flags &= ~0x0010
    line.special = 0
    line.tag = 0
    line.arg0 = 0
    line.arg1 = 0
    line.arg2 = 0
    line.arg3 = 0
    line.arg4 = 0

    track_tex = DOOR_TRACK_TEXTURE
    add_boundary_line(
        map_data,
        v1_idx=line.v1,
        v2_idx=p4_idx,
        right_sector=alcove_sector,
        left_sector=-1,
        right_wall_texture=track_tex,
        left_wall_texture=None,
    )
    panel_line = add_boundary_line(
        map_data,
        v1_idx=p4_idx,
        v2_idx=p3_idx,
        right_sector=alcove_sector,
        left_sector=-1,
        right_wall_texture=panel_texture,
        left_wall_texture=None,
    )
    add_boundary_line(
        map_data,
        v1_idx=p3_idx,
        v2_idx=line.v2,
        right_sector=alcove_sector,
        left_sector=-1,
        right_wall_texture=track_tex,
        left_wall_texture=None,
    )
    if panel_line < 0:
        return None

    wall_center = ((v1.x + v2.x) * 0.5, (v1.y + v2.y) * 0.5)
    return panel_line, room_sector_idx, room_sector, wall_center, tangent, room_normal


def set_exit_marker_hanging_sign(
    map_data: MutableMap,
    room_sector_idx: int,
    room_sector: Sector,
    center: tuple[float, float],
    tangent: tuple[float, float],
    room_normal: tuple[float, float],
    theme: ThemeStyle,
) -> None:
    sign_half = EXIT_SIGN_LONG_UNITS * 0.5
    near = float(EXIT_SIGN_ROOM_OFFSET_UNITS)
    far = near + float(EXIT_SIGN_DEPTH_UNITS)

    near_left = (
        center[0] - tangent[0] * sign_half + room_normal[0] * near,
        center[1] - tangent[1] * sign_half + room_normal[1] * near,
    )
    far_left = (
        center[0] - tangent[0] * sign_half + room_normal[0] * far,
        center[1] - tangent[1] * sign_half + room_normal[1] * far,
    )
    far_right = (
        center[0] + tangent[0] * sign_half + room_normal[0] * far,
        center[1] + tangent[1] * sign_half + room_normal[1] * far,
    )
    near_right = (
        center[0] + tangent[0] * sign_half + room_normal[0] * near,
        center[1] + tangent[1] * sign_half + room_normal[1] * near,
    )

    points = [near_left, near_right, far_right, far_left]
    vertex_indices: list[int] = []
    for x, y in points:
        map_data.vertices.append(Vertex(int(round(x)), int(round(y))))
        vertex_indices.append(len(map_data.vertices) - 1)

    lowered_ceiling = room_sector.ceiling_height - EXIT_SIGN_TEXTURE_HEIGHT_UNITS
    if lowered_ceiling <= room_sector.floor_height + 24:
        return

    sign_sector = add_sector(
        map_data,
        floor_height=room_sector.floor_height,
        ceiling_height=lowered_ceiling,
        floor_texture=room_sector.floor_texture,
        ceiling_texture=room_sector.ceiling_texture,
        light_level=max(96, room_sector.light_level - 4),
    )

    frame_tex = theme.transition_wall_textures[0]
    line_indices = [-1, -1, -1, -1]
    for idx in range(4):
        v1_idx = vertex_indices[idx]
        v2_idx = vertex_indices[(idx + 1) % 4]
        line_idx = add_boundary_line(
            map_data,
            v1_idx=v1_idx,
            v2_idx=v2_idx,
            right_sector=sign_sector,
            left_sector=room_sector_idx,
            right_wall_texture=frame_tex,
            left_wall_texture=frame_tex,
        )
        line_indices[idx] = line_idx

    # Put EXIT on both long sides, matching Doom II's hanging sign style and avoiding normal ambiguity.
    for edge_idx in (0, 2):
        line_idx = line_indices[edge_idx]
        if line_idx < 0:
            continue
        sign_line = map_data.linedefs[line_idx]
        sign_side_idx = -1
        if sign_line.right >= 0 and map_data.sidedefs[sign_line.right].sector == room_sector_idx:
            sign_side_idx = sign_line.right
        elif sign_line.left >= 0 and map_data.sidedefs[sign_line.left].sector == room_sector_idx:
            sign_side_idx = sign_line.left
        if sign_side_idx < 0:
            continue

        sign_side = map_data.sidedefs[sign_side_idx]
        sign_side.texture_top = theme.exit_marker_texture
        sign_side.texture_bottom = "-"
        sign_side.texture_middle = "-"
        sign_side.offset_x = 0
        sign_side.offset_y = 0
        sign_side.offset_x_top = 0
        sign_side.offset_x_bottom = 0
        sign_side.offset_x_middle = 0
        sign_side.offset_y_top = 0
        sign_side.offset_y_bottom = 0
        sign_side.offset_y_middle = 0
        sign_line.flags |= 0x0008
        sign_line.flags &= ~0x0010


def build_exit_alcove_with_hanging_sign(
    map_data: MutableMap,
    panel_line_idx: int,
    theme: ThemeStyle,
) -> int | None:
    if panel_line_idx < 0 or panel_line_idx >= len(map_data.linedefs):
        return None
    built = build_panel_alcove_on_line(
        map_data,
        panel_line_idx,
        theme.switch_texture,
        opening_blocked=False,
    )
    if built is None:
        return None
    switch_line_idx, room_sector_idx, room_sector, center, tangent, room_normal = built
    set_exit_marker_hanging_sign(
        map_data,
        room_sector_idx=room_sector_idx,
        room_sector=room_sector,
        center=center,
        tangent=tangent,
        room_normal=room_normal,
        theme=theme,
    )
    return switch_line_idx


def assign_exit_switch(
    map_data: MutableMap,
    theme: ThemeStyle,
    start_x: int,
    start_y: int,
    preferred_x: int | None = None,
    preferred_y: int | None = None,
    required_front_sector: int | None = None,
) -> None:
    candidate_exit_lines: list[int] = []
    for idx, line in enumerate(map_data.linedefs):
        if line.left >= 0 and line.right >= 0:
            continue
        side_idx = line.right if line.right >= 0 else line.left
        if side_idx < 0:
            continue
        if required_front_sector is not None and map_data.sidedefs[side_idx].sector != required_front_sector:
            continue
        if line_length_sq(map_data, idx) < (64 * 64):
            continue
        candidate_exit_lines.append(idx)

    best_idx: int | None = None
    best_score = -1.0
    for idx in candidate_exit_lines:
        mx, my = line_midpoint(map_data, idx)
        dist_sq = (mx - start_x) ** 2 + (my - start_y) ** 2
        score = dist_sq + line_length_sq(map_data, idx) * 0.25
        if preferred_x is not None and preferred_y is not None:
            pref_dist_sq = (mx - preferred_x) ** 2 + (my - preferred_y) ** 2
            score += max(0.0, 1.0e10 - float(pref_dist_sq))
        if score > best_score:
            best_score = score
            best_idx = idx

    if best_idx is None:
        if required_front_sector is not None:
            raise ValueError(f"{map_data.name}: could not find suitable exit wall in required red-locked room sector.")
        raise ValueError(f"{map_data.name}: could not find suitable exit wall.")

    best_idx = split_one_sided_line_for_center_panel(
        map_data,
        best_idx,
        panel_width=float(EXIT_SWITCH_PANEL_WIDTH_UNITS),
    )
    switch_line_idx = build_exit_alcove_with_hanging_sign(map_data, best_idx, theme)
    if switch_line_idx is None:
        switch_line_idx = best_idx

    line = map_data.linedefs[switch_line_idx]
    set_exit_line_special(line)

    side_idx = line.right if line.right >= 0 else line.left
    if side_idx >= 0:
        side = map_data.sidedefs[side_idx]
        if side.texture_middle == "-":
            side.texture_middle = theme.switch_texture
        side.texture_top = "-"
        side.texture_bottom = "-"


def assign_start_entry_door(
    map_data: MutableMap,
    start_x: int,
    start_y: int,
    start_angle: int,
    required_front_sector: int | None = None,
) -> None:
    # Doom II commonly implies a just-used door behind spawn; replicate it as a static recessed door.
    entry_texture = START_ENTRY_DOOR_TEXTURE
    behind_rad = math.radians((start_angle + 180) % 360)
    behind_vec = (math.cos(behind_rad), math.sin(behind_rad))

    best_idx: int | None = None
    best_score = -1.0e18
    for idx, line in enumerate(map_data.linedefs):
        if line.left >= 0 and line.right >= 0:
            continue
        side_idx = line.right if line.right >= 0 else line.left
        if side_idx < 0:
            continue
        if required_front_sector is not None and map_data.sidedefs[side_idx].sector != required_front_sector:
            continue

        length_sq = line_length_sq(map_data, idx)
        if length_sq < (START_ENTRY_DOOR_WIDTH_UNITS * START_ENTRY_DOOR_WIDTH_UNITS):
            continue

        mx, my = line_midpoint(map_data, idx)
        dx = float(mx - start_x)
        dy = float(my - start_y)
        dist = math.hypot(dx, dy)
        if dist < 48.0 or dist > 1200.0:
            continue
        ux = dx / dist
        uy = dy / dist
        dot = (ux * behind_vec[0]) + (uy * behind_vec[1])
        if dot < 0.30:
            continue
        score = (dot * 1400.0) - dist + (math.sqrt(length_sq) * 0.20)
        if score > best_score:
            best_score = score
            best_idx = idx

    if best_idx is None:
        return

    panel_idx = split_one_sided_line_for_center_panel(
        map_data,
        best_idx,
        panel_width=float(START_ENTRY_DOOR_WIDTH_UNITS),
    )
    build_panel_alcove_on_line(
        map_data,
        panel_idx,
        entry_texture,
        opening_blocked=True,
    )


def add_room_wall_texture_columns(
    map_data: MutableMap,
    layout: PolyLayout,
    room_sector_lookup: dict[int, int],
    theme_name: str,
    rng: random.Random,
    protected_room_indices: set[int] | None = None,
) -> None:
    switch_texture = THEMES.get(theme_name, THEMES["techbase"]).switch_texture
    group_pairs = COLUMN_GROUPS_BY_THEME.get(theme_name, ())
    group_lookup: dict[str, tuple[str, ...]] = {}
    for base, decors in group_pairs:
        merged: list[str] = list(group_lookup.get(base, ()))
        seen = set(merged)
        for decor in decors:
            if decor in seen:
                continue
            merged.append(decor)
            seen.add(decor)
        group_lookup[base] = tuple(merged)
    fallback_pool = ROOM_COLUMN_TEXTURES_BY_THEME.get(theme_name)
    if not group_lookup and not fallback_pool:
        return

    def texture_width_units(texture_name: str) -> int:
        if texture_name in COLUMN_TEXTURE_WIDTH_UNITS:
            return int(COLUMN_TEXTURE_WIDTH_UNITS[texture_name])
        for fallback_name, fallback_width in (fallback_pool or ()):
            if fallback_name == texture_name:
                return int(fallback_width)
        return 64

    def weighted_pick(entries: list[tuple[str, int, int]]) -> tuple[str, int]:
        total = sum(max(1, weight) for _, _, weight in entries)
        roll = rng.uniform(0.0, float(total))
        acc = 0.0
        for texture_name, width_units, weight in entries:
            acc += float(max(1, weight))
            if roll <= acc:
                return texture_name, width_units
        tail_name, tail_width, _ = entries[-1]
        return tail_name, tail_width

    protected = protected_room_indices or set()
    end_margin = 64.0

    for room_idx in range(len(layout.rooms)):
        if room_idx in protected:
            continue
        room_sector = room_sector_lookup.get(room_idx)
        if room_sector is None:
            continue

        target = rng.randint(0, 4)
        if target <= 0:
            continue

        placed = 0
        attempts = 0
        while placed < target and attempts < (target * 12):
            attempts += 1
            candidates: list[tuple[int, list[tuple[str, int, int]]]] = []
            for line_idx, line in enumerate(map_data.linedefs):
                if line.special != 0:
                    continue
                if line.left >= 0 and line.right >= 0:
                    continue
                side_idx = line.right if line.right >= 0 else line.left
                if side_idx < 0:
                    continue
                side = map_data.sidedefs[side_idx]
                if side.sector != room_sector:
                    continue
                if side.texture_middle in {START_ENTRY_DOOR_TEXTURE, switch_texture, "-"}:
                    continue

                line_len = math.sqrt(float(line_length_sq(map_data, line_idx)))
                base_tex = side.texture_middle
                if base_tex in group_lookup:
                    ordered_decor = list(group_lookup[base_tex])
                elif not group_lookup and fallback_pool:
                    ordered_decor = [name for name, _ in fallback_pool]
                else:
                    ordered_decor = []

                fitting: list[tuple[str, int, int]] = []
                for idx, texture_name in enumerate(ordered_decor):
                    if texture_name == base_tex:
                        continue
                    width_units = texture_width_units(texture_name)
                    if line_len < float(width_units) + (2.0 * end_margin):
                        continue
                    # Prefer early entries in ordered lists (higher confidence from research).
                    weight = max(1, len(ordered_decor) - idx)
                    fitting.append((texture_name, width_units, weight))

                if not fitting:
                    continue
                candidates.append((line_idx, fitting))

            if not candidates:
                break

            line_idx, fitting = rng.choice(candidates)
            strip_tex, strip_width = weighted_pick(fitting)
            middle_idx = split_one_sided_line_for_center_panel(
                map_data,
                line_idx,
                panel_width=float(strip_width),
            )
            if middle_idx < 0 or middle_idx >= len(map_data.linedefs):
                continue
            middle = map_data.linedefs[middle_idx]
            side_idx = middle.right if middle.right >= 0 else middle.left
            if side_idx < 0:
                continue
            side = map_data.sidedefs[side_idx]
            if side.sector != room_sector:
                continue

            side.texture_middle = strip_tex
            side.texture_top = "-"
            side.texture_bottom = "-"
            # Start column texture at the segment start instead of inheriting wall offset.
            side.offset_x = 0
            side.offset_x_top = 0
            side.offset_x_bottom = 0
            side.offset_x_middle = 0
            placed += 1


def v_add(a: tuple[float, float], b: tuple[float, float]) -> tuple[float, float]:
    return (a[0] + b[0], a[1] + b[1])


def v_sub(a: tuple[float, float], b: tuple[float, float]) -> tuple[float, float]:
    return (a[0] - b[0], a[1] - b[1])


def v_scale(v: tuple[float, float], s: float) -> tuple[float, float]:
    return (v[0] * s, v[1] * s)


def v_len(v: tuple[float, float]) -> float:
    return math.hypot(v[0], v[1])


def v_norm(v: tuple[float, float]) -> tuple[float, float]:
    length = v_len(v)
    if length < 1.0e-9:
        return (1.0, 0.0)
    return (v[0] / length, v[1] / length)


def v_lerp(a: tuple[float, float], b: tuple[float, float], t: float) -> tuple[float, float]:
    return (a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t)


def v_mid(a: tuple[float, float], b: tuple[float, float]) -> tuple[float, float]:
    return ((a[0] + b[0]) * 0.5, (a[1] + b[1]) * 0.5)


def v_perp(v: tuple[float, float]) -> tuple[float, float]:
    return (-v[1], v[0])


def v_dot(a: tuple[float, float], b: tuple[float, float]) -> float:
    return (a[0] * b[0]) + (a[1] * b[1])


def local_to_world(
    center: tuple[float, float],
    tangent: tuple[float, float],
    normal: tuple[float, float],
    lx: float,
    ly: float,
) -> tuple[float, float]:
    return (
        center[0] + tangent[0] * lx + normal[0] * ly,
        center[1] + tangent[1] * lx + normal[1] * ly,
    )


def build_oriented_room(
    center: tuple[float, float],
    tangent: tuple[float, float],
    half_length: float,
    half_width: float,
    side_bulges: dict[str, float] | None = None,
    l_shape_corner: str | None = None,
    l_shape_cut_length: float = 0.0,
    l_shape_cut_width: float = 0.0,
) -> OrientedRoom:
    t = v_norm(tangent)
    n = v_perp(t)

    back_left = local_to_world(center, t, n, -half_length, half_width)
    front_left = local_to_world(center, t, n, half_length, half_width)
    front_right = local_to_world(center, t, n, half_length, -half_width)
    back_right = local_to_world(center, t, n, -half_length, -half_width)
    polygon = (back_left, front_left, front_right, back_right)

    return OrientedRoom(
        center=center,
        tangent=t,
        normal=n,
        half_length=half_length,
        half_width=half_width,
        polygon=polygon,
        front_left=front_left,
        front_right=front_right,
        back_left=back_left,
        back_right=back_right,
        side_bulges=dict(side_bulges or {}),
        l_shape_corner=l_shape_corner,
        l_shape_cut_length=float(max(0.0, l_shape_cut_length)),
        l_shape_cut_width=float(max(0.0, l_shape_cut_width)),
    )


def generate_room_centers(room_count: int, rng: random.Random) -> list[tuple[float, float]]:
    centers: list[tuple[float, float]] = [(0.0, 0.0)]
    heading = rng.uniform(0.0, math.tau)
    log_trace(f"ROOM_ATTEMPT_ACCEPT idx=0 center=(0.0,0.0) reason=start")

    while len(centers) < room_count:
        prev = centers[-1]
        placed = False
        for attempt in range(48):
            turn = rng.uniform(-1.0, 1.0) if attempt < 16 else rng.uniform(-1.6, 1.6)
            heading_try = heading + turn
            step = rng.uniform(1800.0, 2300.0) * CORRIDOR_LENGTH_SCALE
            candidate = (
                prev[0] + math.cos(heading_try) * step,
                prev[1] + math.sin(heading_try) * step,
            )
            log_trace(
                f"ROOM_ATTEMPT idx={len(centers)} attempt={attempt + 1}/48 "
                f"candidate=({candidate[0]:.1f},{candidate[1]:.1f}) step={step:.1f}"
            )
            if abs(candidate[0]) > 28000 or abs(candidate[1]) > 28000:
                log_trace(
                    f"ROOM_ATTEMPT_REJECT idx={len(centers)} reason=out_of_bounds "
                    f"candidate=({candidate[0]:.1f},{candidate[1]:.1f})"
                )
                continue
            if any(v_len(v_sub(candidate, c)) < 1300.0 for c in centers):
                log_trace(
                    f"ROOM_ATTEMPT_REJECT idx={len(centers)} reason=too_close "
                    f"candidate=({candidate[0]:.1f},{candidate[1]:.1f})"
                )
                continue
            centers.append(candidate)
            heading = heading_try
            log_trace(
                f"ROOM_ATTEMPT_ACCEPT idx={len(centers)-1} center=({candidate[0]:.1f},{candidate[1]:.1f}) "
                f"reason=normal_attempt"
            )
            placed = True
            break

        if not placed:
            step = 1900.0 * CORRIDOR_LENGTH_SCALE
            candidate = (
                prev[0] + math.cos(heading) * step,
                prev[1] + math.sin(heading) * step,
            )
            centers.append(candidate)
            log_trace(
                f"ROOM_ATTEMPT_ACCEPT idx={len(centers)-1} center=({candidate[0]:.1f},{candidate[1]:.1f}) "
                f"reason=fallback"
            )

    return centers


def compute_room_tangents(centers: list[tuple[float, float]]) -> list[tuple[float, float]]:
    n = len(centers)
    if n == 0:
        return []
    if n == 1:
        return [(1.0, 0.0)]

    tangents: list[tuple[float, float]] = []
    for idx in range(n):
        if idx == 0:
            t = v_norm(v_sub(centers[1], centers[0]))
        elif idx == n - 1:
            t = v_norm(v_sub(centers[n - 1], centers[n - 2]))
        else:
            incoming = v_norm(v_sub(centers[idx], centers[idx - 1]))
            outgoing = v_norm(v_sub(centers[idx + 1], centers[idx]))
            combined = v_add(incoming, outgoing)
            t = v_norm(combined) if v_len(combined) > 1.0e-6 else outgoing
        tangents.append(t)
    return tangents


def generate_room_graph(
    room_count: int,
    rng: random.Random,
) -> tuple[list[tuple[float, float]], list[tuple[int, int]]]:
    # Strict campaign flow:
    # 0(start) -> 1(blue branch) -> 3(yellow branch) -> 5(red branch) -> 7(exit)
    # with key dead-ends: 2(blue), 4(yellow), 6(red).
    if room_count in {8, 9, 10}:
        min_center_sep = 1180.0 * CORRIDOR_LENGTH_SCALE
        corridor_room_clear = 1080.0 * CORRIDOR_LENGTH_SCALE
        edge_edge_clear = 360.0 * CORRIDOR_LENGTH_SCALE

        def point_to_segment_dist_sq(
            p: tuple[float, float],
            a: tuple[float, float],
            b: tuple[float, float],
        ) -> float:
            px, py = p
            ax, ay = a
            bx, by = b
            vx = bx - ax
            vy = by - ay
            seg_len_sq = (vx * vx) + (vy * vy)
            if seg_len_sq <= 1.0e-9:
                dx = px - ax
                dy = py - ay
                return (dx * dx) + (dy * dy)
            t = ((px - ax) * vx + (py - ay) * vy) / seg_len_sq
            t = max(0.0, min(1.0, t))
            qx = ax + (vx * t)
            qy = ay + (vy * t)
            dx = px - qx
            dy = py - qy
            return (dx * dx) + (dy * dy)

        def try_build() -> tuple[list[tuple[float, float]], list[tuple[int, int]]] | None:
            centers: dict[int, tuple[float, float]] = {0: (0.0, 0.0)}
            edges_local: list[tuple[int, int]] = []
            heading = rng.uniform(0.0, math.tau)
            base_dir = (math.cos(heading), math.sin(heading))

            def edge_segment_clear(a: int, b: int) -> bool:
                pa = centers[a]
                pb = centers[b]
                for idx, pc in centers.items():
                    if idx in {a, b}:
                        continue
                    if point_to_segment_dist_sq(pc, pa, pb) < (corridor_room_clear * corridor_room_clear):
                        return False
                for u, v in edges_local:
                    if len({a, b, u, v}) < 4:
                        continue
                    pu = centers[u]
                    pv = centers[v]
                    if segment_to_segment_distance_sq(pa, pb, pu, pv) < (edge_edge_clear * edge_edge_clear):
                        return False
                return True

            def candidate_ok(new_idx: int, candidate: tuple[float, float], parents: tuple[int, ...]) -> bool:
                if abs(candidate[0]) > 28000.0 or abs(candidate[1]) > 28000.0:
                    return False
                for idx, c in centers.items():
                    min_sep = min_center_sep
                    if idx in parents:
                        min_sep *= 0.72
                    if v_len(v_sub(candidate, c)) < min_sep:
                        return False
                saved = centers.get(new_idx)
                centers[new_idx] = candidate
                ok = True
                for p in parents:
                    if not edge_segment_clear(p, new_idx):
                        ok = False
                        break
                if saved is None:
                    del centers[new_idx]
                else:
                    centers[new_idx] = saved
                return ok

            def place_from_parent(
                new_idx: int,
                parent: int,
                preferred_dir: tuple[float, float],
                dist_min: float,
                dist_max: float,
                jitter_rad: float = 0.34,
            ) -> bool:
                base_ang = math.atan2(preferred_dir[1], preferred_dir[0])
                for _ in range(96):
                    ang = base_ang + rng.uniform(-jitter_rad, jitter_rad)
                    dist = rng.uniform(dist_min, dist_max) * CORRIDOR_LENGTH_SCALE
                    cand = (
                        centers[parent][0] + math.cos(ang) * dist,
                        centers[parent][1] + math.sin(ang) * dist,
                    )
                    if not candidate_ok(new_idx, cand, (parent,)):
                        continue
                    centers[new_idx] = cand
                    edges_local.append((parent, new_idx))
                    return True
                return False

            if not place_from_parent(1, 0, base_dir, 1450.0, 1750.0):
                return None
            if not place_from_parent(3, 1, base_dir, 1500.0, 1850.0):
                return None
            if not place_from_parent(5, 3, base_dir, 1550.0, 1950.0):
                return None
            if not place_from_parent(7, 5, base_dir, 1500.0, 1900.0):
                return None

            def place_key_dead_end(new_idx: int, parent: int, forward_to: int, prefer_sign: float) -> bool:
                fwd = v_norm(v_sub(centers[forward_to], centers[parent]))
                side = v_perp(fwd)
                for _ in range(96):
                    sign = prefer_sign if rng.random() < 0.68 else -prefer_sign
                    lat = rng.uniform(1250.0, 1750.0) * CORRIDOR_LENGTH_SCALE
                    along = rng.uniform(-180.0, 180.0)
                    cand = v_add(centers[parent], v_add(v_scale(side, sign * lat), v_scale(fwd, along)))
                    if not candidate_ok(new_idx, cand, (parent,)):
                        continue
                    centers[new_idx] = cand
                    edges_local.append((parent, new_idx))
                    return True
                return False

            s1 = 1.0 if rng.random() < 0.5 else -1.0
            s2 = -s1 if rng.random() < 0.7 else (1.0 if rng.random() < 0.5 else -1.0)
            s3 = -s2 if rng.random() < 0.7 else (1.0 if rng.random() < 0.5 else -1.0)
            if not place_key_dead_end(2, 1, 3, s1):
                return None
            if not place_key_dead_end(4, 3, 5, s2):
                return None
            if not place_key_dead_end(6, 5, 7, s3):
                return None

            if room_count == 10:
                pa, pb = rng.choice(((1, 3), (3, 5), (5, 7)))
                mid = v_mid(centers[pa], centers[pb])
                dir_ab = v_norm(v_sub(centers[pb], centers[pa]))
                side = v_perp(dir_ab)
                placed_passage = False
                for _ in range(120):
                    if rng.random() < (1.0 / 3.0):
                        lateral = 0.0
                    else:
                        lateral = rng.uniform(520.0, 980.0) * (1.0 if rng.random() < 0.5 else -1.0)
                    along = rng.uniform(-180.0, 180.0)
                    cand = v_add(mid, v_add(v_scale(side, lateral), v_scale(dir_ab, along)))
                    if not candidate_ok(8, cand, (pa, pb)):
                        continue
                    centers[8] = cand
                    edges_local = [e for e in edges_local if set(e) != {pa, pb}]
                    edges_local.append((pa, 8))
                    edges_local.append((8, pb))
                    placed_passage = True
                    break
                if not placed_passage:
                    return None

            if room_count in {9, 10}:
                bonus_idx = 8 if room_count == 9 else 9
                bonus_parent = rng.choice((1, 3, 5))
                forward_to = 3 if bonus_parent == 1 else (5 if bonus_parent == 3 else 7)
                fwd = v_norm(v_sub(centers[forward_to], centers[bonus_parent]))
                side = v_perp(fwd)
                placed_bonus = False
                for _ in range(96):
                    sign = 1.0 if rng.random() < 0.5 else -1.0
                    lat = rng.uniform(1200.0, 1650.0) * CORRIDOR_LENGTH_SCALE
                    along = rng.uniform(-180.0, 180.0)
                    cand = v_add(centers[bonus_parent], v_add(v_scale(side, sign * lat), v_scale(fwd, along)))
                    if not candidate_ok(bonus_idx, cand, (bonus_parent,)):
                        continue
                    centers[bonus_idx] = cand
                    edges_local.append((bonus_parent, bonus_idx))
                    placed_bonus = True
                    break
                if not placed_bonus:
                    return None

            ordered_centers = [centers[idx] for idx in range(room_count)]
            return ordered_centers, edges_local

        for _ in range(120):
            built = try_build()
            if built is not None:
                return built
        raise ValueError("strict room graph placement failed")

    main_count = max(6, min(room_count, int(round(room_count * 0.55))))
    main_centers = generate_room_centers(main_count, rng)
    main_tangents = compute_room_tangents(main_centers)

    centers = main_centers[:]
    edges: list[tuple[int, int]] = [(idx, idx + 1) for idx in range(main_count - 1)]
    max_degree = 3
    degree = [0 for _ in range(main_count)]
    for a, b in edges:
        degree[a] += 1
        degree[b] += 1

    while len(centers) < room_count:
        anchors = [idx for idx, deg in enumerate(degree) if deg < max_degree]
        if not anchors:
            anchors = list(range(len(centers)))
        interior = [idx for idx in anchors if 1 <= idx < main_count - 1]
        anchor = rng.choice(interior if interior else anchors)
        anchor_center = centers[anchor]
        if anchor < len(main_tangents):
            base_tangent = main_tangents[anchor]
        else:
            neighbors = [b if a == anchor else a for a, b in edges if a == anchor or b == anchor]
            if neighbors:
                base_tangent = v_norm(v_sub(anchor_center, centers[neighbors[0]]))
            else:
                angle = rng.uniform(0.0, math.tau)
                base_tangent = (math.cos(angle), math.sin(angle))

        placed = False
        for _ in range(48):
            side_sign = 1.0 if rng.random() < 0.5 else -1.0
            side_dir = v_scale(v_perp(base_tangent), side_sign)
            drift = rng.uniform(-0.35, 0.35)
            branch_dir = v_norm(v_add(side_dir, v_scale(base_tangent, drift)))
            distance = rng.uniform(1600.0, 2400.0) * CORRIDOR_LENGTH_SCALE
            candidate = v_add(anchor_center, v_scale(branch_dir, distance))
            log_trace(
                f"ROOM_ATTEMPT idx={len(centers)} attempt=branch "
                f"anchor={anchor} candidate=({candidate[0]:.1f},{candidate[1]:.1f}) dist={distance:.1f}"
            )
            if abs(candidate[0]) > 28000.0 or abs(candidate[1]) > 28000.0:
                log_trace(
                    f"ROOM_ATTEMPT_REJECT idx={len(centers)} reason=out_of_bounds "
                    f"candidate=({candidate[0]:.1f},{candidate[1]:.1f})"
                )
                continue
            if any(v_len(v_sub(candidate, center)) < 1450.0 for center in centers):
                log_trace(
                    f"ROOM_ATTEMPT_REJECT idx={len(centers)} reason=too_close "
                    f"candidate=({candidate[0]:.1f},{candidate[1]:.1f})"
                )
                continue
            centers.append(candidate)
            edges.append((anchor, len(centers) - 1))
            degree[anchor] += 1
            degree.append(1)
            log_trace(
                f"ROOM_ATTEMPT_ACCEPT idx={len(centers)-1} center=({candidate[0]:.1f},{candidate[1]:.1f}) "
                f"reason=branch anchor={anchor}"
            )
            placed = True
            break

        if not placed:
            fallback_angle = rng.uniform(0.0, math.tau)
            fallback = (
                anchor_center[0] + math.cos(fallback_angle) * (1900.0 * CORRIDOR_LENGTH_SCALE),
                anchor_center[1] + math.sin(fallback_angle) * (1900.0 * CORRIDOR_LENGTH_SCALE),
            )
            centers.append(fallback)
            edges.append((anchor, len(centers) - 1))
            degree[anchor] += 1
            degree.append(1)
            log_trace(
                f"ROOM_ATTEMPT_ACCEPT idx={len(centers)-1} center=({fallback[0]:.1f},{fallback[1]:.1f}) "
                f"reason=branch_fallback anchor={anchor}"
            )

    return centers, edges


def compute_room_tangents_from_graph(
    centers: list[tuple[float, float]],
    edges: list[tuple[int, int]],
) -> list[tuple[float, float]]:
    adjacency: list[list[int]] = [[] for _ in centers]
    for a, b in edges:
        if 0 <= a < len(centers) and 0 <= b < len(centers):
            adjacency[a].append(b)
            adjacency[b].append(a)

    tangents: list[tuple[float, float]] = []
    for idx, neighbors in enumerate(adjacency):
        if not neighbors:
            tangents.append((1.0, 0.0))
            continue
        vectors = [v_norm(v_sub(centers[n], centers[idx])) for n in neighbors]
        sx = sum(v[0] for v in vectors)
        sy = sum(v[1] for v in vectors)
        if abs(sx) < 1.0e-6 and abs(sy) < 1.0e-6:
            tangents.append(vectors[0])
        else:
            tangents.append(v_norm((sx, sy)))
    return tangents


def projected_room_half_extent(
    half_length: float,
    half_width: float,
    tangent: tuple[float, float],
    normal: tuple[float, float],
    direction: tuple[float, float],
) -> float:
    along_tangent = abs(v_dot(direction, tangent)) * float(half_length)
    along_normal = abs(v_dot(direction, normal)) * float(half_width)
    return along_tangent + along_normal


def relax_room_centers_for_corridor_clearance(
    centers: list[tuple[float, float]],
    edges: list[tuple[int, int]],
    room_half_sizes: list[tuple[float, float]],
) -> list[tuple[float, float]]:
    if not centers:
        return []
    relaxed = [(float(x), float(y)) for x, y in centers]
    edge_pairs = {
        (min(a, b), max(a, b))
        for a, b in edges
        if 0 <= a < len(relaxed) and 0 <= b < len(relaxed) and a != b
    }
    n = len(relaxed)
    if len(room_half_sizes) < n:
        return relaxed

    spacing_scale = 1.12  # Keep spread increase modest (~10-15%).
    corridor_half_max = (96.0 + 32.0 + 8.0) * CORRIDOR_GEOMETRY_SCALE
    corridor_room_margin = 56.0 * spacing_scale

    for _ in range(ROOM_CENTER_RELAXATION_PASSES):
        tangents = compute_room_tangents_from_graph(relaxed, edges)
        normals = [v_perp(t) for t in tangents]
        moved = False
        for i in range(n):
            for j in range(i + 1, n):
                connected = (i, j) in edge_pairs
                base_gap = CONNECTED_ROOM_WALL_GAP_UNITS if connected else UNCONNECTED_ROOM_WALL_GAP_UNITS
                desired_gap = base_gap * spacing_scale
                if desired_gap <= 0.0:
                    continue

                ix, iy = relaxed[i]
                jx, jy = relaxed[j]
                dx = jx - ix
                dy = jy - iy
                dist = math.hypot(dx, dy)
                if dist <= 1.0e-6:
                    direction = (1.0, 0.0)
                    dist = 1.0e-6
                else:
                    direction = (dx / dist, dy / dist)

                i_half_len, i_half_wid = room_half_sizes[i]
                j_half_len, j_half_wid = room_half_sizes[j]
                i_extent = projected_room_half_extent(i_half_len, i_half_wid, tangents[i], normals[i], direction)
                j_extent = projected_room_half_extent(j_half_len, j_half_wid, tangents[j], normals[j], direction)
                gap = dist - i_extent - j_extent
                if gap >= desired_gap:
                    continue

                deficit = desired_gap - gap
                if i == 0 and j != 0:
                    move_i = deficit * 0.15
                    move_j = deficit - move_i
                elif j == 0 and i != 0:
                    move_j = deficit * 0.15
                    move_i = deficit - move_j
                else:
                    move_i = deficit * 0.5
                    move_j = deficit * 0.5

                relaxed[i] = (ix - (direction[0] * move_i), iy - (direction[1] * move_i))
                relaxed[j] = (jx + (direction[0] * move_j), jy + (direction[1] * move_j))
                moved = True

        # Additional safety pass: keep non-endpoint rooms away from planned
        # corridor centerlines to reduce room/corridor intersection risk.
        for a, b in edges:
            if not (0 <= a < n and 0 <= b < n) or a == b:
                continue
            ax, ay = relaxed[a]
            bx, by = relaxed[b]
            sx = bx - ax
            sy = by - ay
            seg_len_sq = (sx * sx) + (sy * sy)
            if seg_len_sq <= 1.0e-6:
                continue
            seg_len = math.sqrt(seg_len_sq)
            seg_dir = (sx / seg_len, sy / seg_len)
            seg_perp = v_perp(seg_dir)

            for k in range(n):
                if k == a or k == b:
                    continue
                cx, cy = relaxed[k]
                t = ((cx - ax) * sx + (cy - ay) * sy) / seg_len_sq
                t = max(0.0, min(1.0, t))
                qx = ax + (sx * t)
                qy = ay + (sy * t)
                ox = cx - qx
                oy = cy - qy
                off_len = math.hypot(ox, oy)
                if off_len <= 1.0e-6:
                    side_sign = 1.0 if ((a + b + k) % 2 == 0) else -1.0
                    away = (seg_perp[0] * side_sign, seg_perp[1] * side_sign)
                    off_len = 1.0e-6
                else:
                    away = (ox / off_len, oy / off_len)

                k_half_len, k_half_wid = room_half_sizes[k]
                k_extent = projected_room_half_extent(
                    k_half_len,
                    k_half_wid,
                    tangents[k],
                    normals[k],
                    away,
                )
                required = k_extent + corridor_half_max + corridor_room_margin
                if off_len >= required:
                    continue

                deficit = required - off_len
                push = deficit * (0.15 if k == 0 else 1.0)
                relaxed[k] = (cx + (away[0] * push), cy + (away[1] * push))
                moved = True
        if not moved:
            break

    return relaxed


def relax_room_centers_for_corridor_room_intersections(
    centers: list[tuple[float, float]],
    edges: list[tuple[int, int]],
    room_templates: list[tuple[float, float, dict[str, float], str | None, float, float]],
) -> list[tuple[float, float]]:
    if not centers:
        return []
    n = len(centers)
    if len(room_templates) < n:
        return list(centers)

    relaxed = [(float(x), float(y)) for x, y in centers]
    corridor_half_max = (96.0 + 32.0 + 8.0) * CORRIDOR_GEOMETRY_SCALE
    required_clearance = corridor_half_max + 72.0
    required_clearance_sq = required_clearance * required_clearance
    bbox_margin = 64.0

    def room_radius(idx: int) -> float:
        half_length, half_width, side_bulges, _, _, _ = room_templates[idx]
        bulge = max((float(v) for v in side_bulges.values()), default=0.0)
        return math.hypot(half_length + bulge, half_width + bulge)

    def build_expanded_bboxes(rooms_preview: list[OrientedRoom]) -> list[tuple[float, float, float, float]]:
        boxes: list[tuple[float, float, float, float]] = []
        for room in rooms_preview:
            xs = [p[0] for p in room.polygon]
            ys = [p[1] for p in room.polygon]
            boxes.append(
                (
                    min(xs) - bbox_margin,
                    max(xs) + bbox_margin,
                    min(ys) - bbox_margin,
                    max(ys) + bbox_margin,
                )
            )
        return boxes

    def segment_hits_bbox(
        a: tuple[float, float],
        b: tuple[float, float],
        bbox: tuple[float, float, float, float],
    ) -> bool:
        minx, maxx, miny, maxy = bbox
        ax, ay = a
        bx, by = b
        if minx <= ax <= maxx and miny <= ay <= maxy:
            return True
        if minx <= bx <= maxx and miny <= by <= maxy:
            return True
        box_edges = (
            ((minx, miny), (maxx, miny)),
            ((maxx, miny), (maxx, maxy)),
            ((maxx, maxy), (minx, maxy)),
            ((minx, maxy), (minx, miny)),
        )
        for edge_a, edge_b in box_edges:
            if segment_to_segment_distance_sq(a, b, edge_a, edge_b) <= 1e-6:
                return True
        return False

    def compute_depth_and_parent() -> tuple[list[int], list[int]]:
        adjacency: list[list[int]] = [[] for _ in range(n)]
        for i, j in edges:
            if 0 <= i < n and 0 <= j < n and i != j:
                adjacency[i].append(j)
                adjacency[j].append(i)
        depth = [10**9 for _ in range(n)]
        parent = [-1 for _ in range(n)]
        depth[0] = 0
        queue: deque[int] = deque([0])
        while queue:
            node = queue.popleft()
            for nxt in adjacency[node]:
                if depth[nxt] <= depth[node] + 1:
                    continue
                depth[nxt] = depth[node] + 1
                parent[nxt] = node
                queue.append(nxt)
        return depth, parent

    def try_reanchor_room(
        moving_idx: int,
        anchor_idx: int,
        boxes: list[tuple[float, float, float, float]],
    ) -> bool:
        if moving_idx == 0 or moving_idx == anchor_idx:
            return False
        if not (0 <= moving_idx < n and 0 <= anchor_idx < n):
            return False

        ax, ay = relaxed[anchor_idx]
        mx, my = relaxed[moving_idx]
        base_vec = v_sub((mx, my), (ax, ay))
        base_len = v_len(base_vec)
        if base_len <= 1.0e-6:
            angle = math.radians(float(((moving_idx + 1) * 67) % 360))
            base = (math.cos(angle), math.sin(angle))
            base_len = 1700.0 * CORRIDOR_LENGTH_SCALE
        else:
            base = (base_vec[0] / base_len, base_vec[1] / base_len)

        perp = v_perp(base)
        diag0 = v_norm(v_add(base, perp))
        diag1 = v_norm(v_sub(base, perp))
        candidate_dirs = [
            base,
            perp,
            v_scale(perp, -1.0),
            v_scale(base, -1.0),
            diag0,
            diag1,
            v_scale(diag0, -1.0),
            v_scale(diag1, -1.0),
        ]
        step = max(base_len, 1700.0 * CORRIDOR_LENGTH_SCALE)
        candidate_dists = [step, step * 1.18, step * 1.34]
        moving_radius = room_radius(moving_idx)

        best_center: tuple[float, float] | None = None
        best_score = -1.0e18
        for direction in candidate_dirs:
            for dist in candidate_dists:
                cand = (ax + (direction[0] * dist), ay + (direction[1] * dist))
                seg = ((ax, ay), cand)
                valid = True
                min_clear = 1.0e18
                for other in range(n):
                    if other in {moving_idx, anchor_idx}:
                        continue
                    ox, oy = relaxed[other]
                    center_dist = math.hypot(cand[0] - ox, cand[1] - oy)
                    min_clear = min(min_clear, center_dist)
                    if center_dist < (moving_radius + room_radius(other) + 160.0):
                        valid = False
                        break
                    if segment_hits_bbox(seg[0], seg[1], boxes[other]):
                        valid = False
                        break
                if not valid:
                    continue
                score = min_clear - (0.03 * dist)
                if score > best_score:
                    best_score = score
                    best_center = cand

        if best_center is None:
            return False
        relaxed[moving_idx] = best_center
        return True

    for _ in range(max(10, ROOM_CENTER_RELAXATION_PASSES // 2)):
        tangents = compute_room_tangents_from_graph(relaxed, edges)
        rooms_preview: list[OrientedRoom] = []
        for idx, center in enumerate(relaxed):
            half_length, half_width, side_bulges, l_shape_corner, l_cut_len, l_cut_wid = room_templates[idx]
            rooms_preview.append(
                build_oriented_room(
                    center,
                    tangents[idx],
                    half_length,
                    half_width,
                    side_bulges=dict(side_bulges),
                    l_shape_corner=l_shape_corner,
                    l_shape_cut_length=l_cut_len,
                    l_shape_cut_width=l_cut_wid,
                )
            )
        boxes = build_expanded_bboxes(rooms_preview)
        depth, parent = compute_depth_and_parent()

        moved = False
        restarted = False
        for a, b in edges:
            if not (0 <= a < n and 0 <= b < n) or a == b:
                continue
            ax, ay = relaxed[a]
            bx, by = relaxed[b]
            sx = bx - ax
            sy = by - ay
            seg_len_sq = (sx * sx) + (sy * sy)
            if seg_len_sq <= 1.0e-6:
                continue
            seg_len = math.sqrt(seg_len_sq)
            seg_dir = (sx / seg_len, sy / seg_len)
            seg_perp = v_perp(seg_dir)
            seg_mid = ((ax + bx) * 0.5, (ay + by) * 0.5)
            segment = [((ax, ay), (bx, by))]

            for k in range(n):
                if k == a or k == b:
                    continue
                room_poly = rooms_preview[k].polygon
                if len(room_poly) < 3:
                    continue

                crosses_room = (
                    point_in_polygon((ax, ay), room_poly)
                    or point_in_polygon((bx, by), room_poly)
                    or point_in_polygon(seg_mid, room_poly)
                )
                edge_dist_sq = min_edge_distance_polygon_to_segments_sq(room_poly, segment)
                if not crosses_room and edge_dist_sq >= required_clearance_sq:
                    continue

                # If corridor route between (a,b) conflicts with another room,
                # prefer replacing the target room position rather than only
                # nudging the intersected room away.
                if depth[a] <= depth[b]:
                    moving_idx = b
                    anchor_idx = a
                else:
                    moving_idx = a
                    anchor_idx = b
                if parent[moving_idx] >= 0:
                    anchor_idx = parent[moving_idx]
                if try_reanchor_room(moving_idx, anchor_idx, boxes):
                    moved = True
                    restarted = True
                    break

                cx, cy = relaxed[k]
                t = ((cx - ax) * sx + (cy - ay) * sy) / seg_len_sq
                t = max(0.0, min(1.0, t))
                qx = ax + (sx * t)
                qy = ay + (sy * t)
                ox = cx - qx
                oy = cy - qy
                off_len = math.hypot(ox, oy)
                if off_len <= 1.0e-6:
                    side_sign = 1.0 if ((a + b + k) % 2 == 0) else -1.0
                    away = (seg_perp[0] * side_sign, seg_perp[1] * side_sign)
                    off_len = 1.0e-6
                else:
                    away = (ox / off_len, oy / off_len)

                deficit = required_clearance - off_len
                if crosses_room:
                    deficit = max(deficit, required_clearance * 0.6)
                if deficit <= 0.0:
                    continue
                push = deficit * (0.15 if k == 0 else 1.0)
                relaxed[k] = (cx + (away[0] * push), cy + (away[1] * push))
                moved = True
            if restarted:
                break

        if not moved:
            break
    return relaxed


def assign_room_floor_heights(
    room_count: int,
    edges: list[tuple[int, int]],
    centers: list[tuple[float, float]],
    rng: random.Random,
) -> list[int]:
    if room_count <= 0:
        return []
    adjacency: list[list[int]] = [[] for _ in range(room_count)]
    edge_delta_cap: dict[frozenset[int], int] = {}

    def max_edge_delta(a: int, b: int) -> int:
        if not (0 <= a < len(centers) and 0 <= b < len(centers)):
            return CORRIDOR_MAX_ADJ_STEP * 4
        ax, ay = centers[a]
        bx, by = centers[b]
        line_len = max(1.0, math.hypot(bx - ax, by - ay))
        segment_count = max(10, int(line_len / 112.0))
        fixed_start = 0
        fixed_end = 0
        for idx in range(segment_count):
            t0 = idx / segment_count
            t1 = (idx + 1) / segment_count
            mid = ((t0 + t1) * 0.5) * line_len
            if mid < CORRIDOR_END_FLAT_UNITS:
                fixed_start += 1
            if (line_len - mid) < CORRIDOR_END_FLAT_UNITS:
                fixed_end += 1
        start_last = max(0, fixed_start - 1)
        end_first = min(segment_count - 1, segment_count - fixed_end)
        transitions = max(1, end_first - start_last)
        return max(CORRIDOR_MAX_ADJ_STEP, transitions * CORRIDOR_MAX_ADJ_STEP)

    for a, b in edges:
        if 0 <= a < room_count and 0 <= b < room_count:
            adjacency[a].append(b)
            adjacency[b].append(a)
            edge_delta_cap[frozenset((a, b))] = max_edge_delta(a, b)

    floors: list[int | None] = [None for _ in range(room_count)]
    floors[0] = 0
    queue: deque[int] = deque([0])
    while queue:
        node = queue.popleft()
        base = int(floors[node] or 0)
        for nxt in adjacency[node]:
            if floors[nxt] is not None:
                continue
            edge_cap = edge_delta_cap.get(frozenset((node, nxt)), ROOM_FLOOR_EDGE_DELTA_MAX)
            edge_cap = max(0, min(ROOM_FLOOR_EDGE_DELTA_MAX, edge_cap))
            if rng.random() < 0.50:
                delta = 0
            else:
                delta = rng.randint(-edge_cap, edge_cap)
                delta = int(round(delta / 8.0) * 8)
            level = max(-ROOM_FLOOR_VARIATION_MAX, min(ROOM_FLOOR_VARIATION_MAX, base + delta))
            level = int(round(level / 8.0) * 8)
            floors[nxt] = level
            queue.append(nxt)

    for idx, value in enumerate(floors):
        if value is None:
            floors[idx] = 0
    return [int(v) for v in floors]


def room_side_segment(
    room: OrientedRoom,
    side: str,
) -> tuple[tuple[float, float], tuple[float, float]]:
    if side == "front":
        return room.front_left, room.front_right
    if side == "back":
        return room.back_right, room.back_left
    if side == "left":
        return room.back_left, room.front_left
    if side == "right":
        return room.front_right, room.back_right
    return room.front_left, room.front_right


def room_side_effective_segment(
    room: OrientedRoom,
    side: str,
) -> tuple[tuple[float, float], tuple[float, float]] | None:
    start, end = room_side_segment(room, side)
    edge = v_sub(end, start)
    edge_len = max(1.0e-6, v_len(edge))
    edge_dir = v_scale(edge, 1.0 / edge_len)

    trim_start = {"left": 0.0, "front": 0.0, "right": 0.0, "back": 0.0}
    trim_end = {"left": 0.0, "front": 0.0, "right": 0.0, "back": 0.0}
    corner = room.l_shape_corner
    cut_len = min(max(0.0, float(room.l_shape_cut_length)), (2.0 * room.half_length) * 0.75)
    cut_wid = min(max(0.0, float(room.l_shape_cut_width)), (2.0 * room.half_width) * 0.75)
    if corner and cut_len > 1.0 and cut_wid > 1.0:
        if corner == "front_left":
            trim_end["left"] = cut_len
            trim_start["front"] = cut_wid
        elif corner == "front_right":
            trim_end["front"] = cut_wid
            trim_start["right"] = cut_len
        elif corner == "back_right":
            trim_end["right"] = cut_len
            trim_start["back"] = cut_wid
        elif corner == "back_left":
            trim_end["back"] = cut_wid
            trim_start["left"] = cut_len

    seg_start_d = max(0.0, min(edge_len, trim_start[side]))
    seg_end_d = max(0.0, min(edge_len, edge_len - trim_end[side]))
    if seg_end_d <= seg_start_d + 1.0e-3:
        return None
    seg_start = v_add(start, v_scale(edge_dir, seg_start_d))
    seg_end = v_add(start, v_scale(edge_dir, seg_end_d))
    return seg_start, seg_end


def point_in_room_local_shape(room: OrientedRoom, lx: float, ly: float) -> bool:
    if lx < -room.half_length or lx > room.half_length or ly < -room.half_width or ly > room.half_width:
        return False
    if not room.l_shape_corner or room.l_shape_cut_length <= 1.0 or room.l_shape_cut_width <= 1.0:
        return True

    corner = room.l_shape_corner
    cl = room.l_shape_cut_length
    cw = room.l_shape_cut_width
    if corner == "front_left":
        return not (lx >= (room.half_length - cl) and ly >= (room.half_width - cw))
    if corner == "front_right":
        return not (lx >= (room.half_length - cl) and ly <= (-room.half_width + cw))
    if corner == "back_right":
        return not (lx <= (-room.half_length + cl) and ly <= (-room.half_width + cw))
    if corner == "back_left":
        return not (lx <= (-room.half_length + cl) and ly >= (room.half_width - cw))
    return True


def polygon_inside_room_local_shape(room: OrientedRoom, poly: list[tuple[float, float]]) -> bool:
    if len(poly) < 3:
        return False
    for idx in range(len(poly)):
        x1, y1 = poly[idx]
        x2, y2 = poly[(idx + 1) % len(poly)]
        if not point_in_room_local_shape(room, x1, y1):
            return False
        # Edge midpoint catches segments that pass through an L-cut void.
        if not point_in_room_local_shape(room, (x1 + x2) * 0.5, (y1 + y2) * 0.5):
            return False
    return True


def room_side_forward(room: OrientedRoom, side: str) -> tuple[float, float]:
    if side == "front":
        return room.tangent
    if side == "back":
        return v_scale(room.tangent, -1.0)
    if side == "left":
        return room.normal
    if side == "right":
        return v_scale(room.normal, -1.0)
    return room.tangent


def choose_room_side(
    room: OrientedRoom,
    corridor_dir: tuple[float, float],
    used: set[str],
    min_door_width: float = float(DOOR_NATIVE_WIDTH),
) -> str:
    scores = {
        "front": v_dot(corridor_dir, room.tangent),
        "back": -v_dot(corridor_dir, room.tangent),
        "left": v_dot(corridor_dir, room.normal),
        "right": -v_dot(corridor_dir, room.normal),
    }
    ordered = sorted(scores.items(), key=lambda item: item[1], reverse=True)
    def is_wide_enough(side: str) -> bool:
        seg = room_side_effective_segment(room, side)
        if seg is None:
            return False
        return v_len(v_sub(seg[1], seg[0])) >= float(min_door_width)

    for side, _score in ordered:
        if side not in used and is_wide_enough(side):
            return side
    for side, _score in ordered:
        if is_wide_enough(side):
            return side
    for side, _score in ordered:
        if side not in used:
            return side
    return ordered[0][0]


def orient_segment_for_direction(
    p1: tuple[float, float],
    p2: tuple[float, float],
    corridor_dir: tuple[float, float],
) -> tuple[tuple[float, float], tuple[float, float]]:
    left_hint = v_perp(corridor_dir)
    if v_dot(v_sub(p1, p2), left_hint) >= 0.0:
        return p1, p2
    return p2, p1


def door_segment_on_side(
    room: OrientedRoom,
    side: str,
    width: float,
    rng: random.Random,
) -> tuple[tuple[float, float], tuple[float, float]]:
    seg = room_side_effective_segment(room, side)
    if seg is None:
        side_start, side_end = room_side_segment(room, side)
    else:
        side_start, side_end = seg
    edge = v_sub(side_end, side_start)
    edge_len = max(1.0, v_len(edge))
    edge_dir = v_scale(edge, 1.0 / edge_len)
    half = min(width * 0.5, edge_len * 0.45)
    mid = v_mid(side_start, side_end)
    # Keep a safety margin from corners, then allow bounded random offset.
    center_margin = max(DOOR_RANDOM_OFFSET_MIN_MARGIN_UNITS, width * 0.125)
    max_center_offset = max(0.0, (edge_len * 0.5) - half - center_margin)
    if max_center_offset > 0.0:
        offset_limit = min(max_center_offset, edge_len * DOOR_RANDOM_OFFSET_MAX_FRACTION)
        mid = v_add(mid, v_scale(edge_dir, rng.uniform(-offset_limit, offset_limit)))
    p1 = v_sub(mid, v_scale(edge_dir, half))
    p2 = v_add(mid, v_scale(edge_dir, half))
    return p1, p2


def build_recess_endpoint(
    raw_door_segment: tuple[tuple[float, float], tuple[float, float]],
    outward: tuple[float, float],
) -> dict[str, tuple[tuple[float, float], tuple[float, float]] | tuple[tuple[float, float], ...]]:
    # Flat alcove profile with a 1-unit micro-alcove at the door front.
    # depth 0..24: flat alcove
    # depth 24..25: micro-alcove (lintel + marker reserve strips)
    # depth 25..(25 + DOOR_THICKNESS): centered door slab
    out = v_norm(outward)
    left0, right0 = orient_segment_for_direction(raw_door_segment[0], raw_door_segment[1], out)
    side_axis = v_norm(v_sub(left0, right0))
    center = v_mid(left0, right0)

    def pt(depth: float, side_off: float) -> tuple[float, float]:
        c = v_add(center, v_scale(out, depth))
        return v_add(c, v_scale(side_axis, side_off))

    wall_left = pt(0.0, 96.0)
    wall_right = pt(0.0, -96.0)
    outer_left = pt(64.0, 96.0)
    outer_right = pt(64.0, -96.0)

    recess_front_depth = 24.0
    # Keep lintel/jamb strip width unchanged, but make the strip depth minimal.
    micro_alcove_depth = 1.0
    door_inner_depth = recess_front_depth + micro_alcove_depth
    door_outer_depth = door_inner_depth + float(DOOR_THICKNESS)
    d24_l96 = pt(recess_front_depth, 96.0)
    d24_l72 = pt(recess_front_depth, 72.0)
    d24_l64 = pt(recess_front_depth, 64.0)
    d24_r64 = pt(recess_front_depth, -64.0)
    d24_r72 = pt(recess_front_depth, -72.0)
    d24_r96 = pt(recess_front_depth, -96.0)

    d25_l96 = pt(door_inner_depth, 96.0)
    d25_l72 = pt(door_inner_depth, 72.0)
    d25_l64 = pt(door_inner_depth, 64.0)
    d25_r64 = pt(door_inner_depth, -64.0)
    d25_r72 = pt(door_inner_depth, -72.0)
    d25_r96 = pt(door_inner_depth, -96.0)

    d33_l96 = pt(door_outer_depth, 96.0)
    d33_l72 = pt(door_outer_depth, 72.0)
    d33_l64 = pt(door_outer_depth, 64.0)
    d33_r64 = pt(door_outer_depth, -64.0)
    d33_r72 = pt(door_outer_depth, -72.0)
    d33_r96 = pt(door_outer_depth, -96.0)

    corridor_micro_depth = door_outer_depth + micro_alcove_depth
    d34_l96 = pt(corridor_micro_depth, 96.0)
    d34_l72 = pt(corridor_micro_depth, 72.0)
    d34_l64 = pt(corridor_micro_depth, 64.0)
    d34_r64 = pt(corridor_micro_depth, -64.0)
    d34_r72 = pt(corridor_micro_depth, -72.0)
    d34_r96 = pt(corridor_micro_depth, -96.0)

    return {
        "wall_open": (wall_left, wall_right),
        "corridor_open": (outer_left, outer_right),
        "inner_poly": (
            wall_right,
            d24_r96,
            d24_r72,
            d24_r64,
            d24_l64,
            d24_l72,
            d24_l96,
            wall_left,
        ),
        "micro_lintel_poly": (d24_r64, d25_r64, d25_l64, d24_l64),
        "micro_lintel_back_poly": (d33_r64, d34_r64, d34_l64, d33_l64),
        "door_poly": (d25_r64, d33_r64, d33_l64, d25_l64),
        "side_left_marker_poly": (d24_l64, d25_l64, d25_l72, d24_l72),
        "side_right_marker_poly": (d24_r72, d25_r72, d25_r64, d24_r64),
        "side_left_marker_back_poly": (d33_l64, d34_l64, d34_l72, d33_l72),
        "side_right_marker_back_poly": (d33_r72, d34_r72, d34_r64, d33_r64),
        "side_left_plain_poly": (d24_l72, d33_l72, d33_l96, d24_l96),
        "side_right_plain_poly": (d24_r96, d33_r96, d33_r72, d24_r72),
        "outer_poly": (
            d34_r96,
            d34_r72,
            d34_r64,
            d34_l64,
            d34_l72,
            d34_l96,
            outer_left,
            outer_right,
        ),
        "open_poly": (wall_right, outer_right, outer_left, wall_left),
    }


def cubic_bezier(
    p0: tuple[float, float],
    p1: tuple[float, float],
    p2: tuple[float, float],
    p3: tuple[float, float],
    t: float,
) -> tuple[float, float]:
    u = 1.0 - t
    a = u * u * u
    b = 3.0 * u * u * t
    c = 3.0 * u * t * t
    d = t * t * t
    return (
        (p0[0] * a) + (p1[0] * b) + (p2[0] * c) + (p3[0] * d),
        (p0[1] * a) + (p1[1] * b) + (p2[1] * c) + (p3[1] * d),
    )


def cubic_bezier_derivative(
    p0: tuple[float, float],
    p1: tuple[float, float],
    p2: tuple[float, float],
    p3: tuple[float, float],
    t: float,
) -> tuple[float, float]:
    u = 1.0 - t
    a = 3.0 * u * u
    b = 6.0 * u * t
    c = 3.0 * t * t
    return (
        ((p1[0] - p0[0]) * a) + ((p2[0] - p1[0]) * b) + ((p3[0] - p2[0]) * c),
        ((p1[1] - p0[1]) * a) + ((p2[1] - p1[1]) * b) + ((p3[1] - p2[1]) * c),
    )


def room_polygon_with_door_splits(
    room: OrientedRoom,
    side_doors: dict[str, list[tuple[tuple[float, float], tuple[float, float]]]],
) -> tuple[tuple[float, float], ...]:
    corners = {
        "bl": room.back_left,
        "fl": room.front_left,
        "fr": room.front_right,
        "br": room.back_right,
    }
    sides = [
        ("left", corners["bl"], corners["fl"]),
        ("front", corners["fl"], corners["fr"]),
        ("right", corners["fr"], corners["br"]),
        ("back", corners["br"], corners["bl"]),
    ]

    eps = 1.0e-3
    points: list[tuple[float, float]] = []

    def append_point(point: tuple[float, float]) -> None:
        if not points or v_len(v_sub(points[-1], point)) > eps:
            points.append(point)

    trim_start = {"left": 0.0, "front": 0.0, "right": 0.0, "back": 0.0}
    trim_end = {"left": 0.0, "front": 0.0, "right": 0.0, "back": 0.0}
    l_corner = room.l_shape_corner
    cut_len = min(max(0.0, float(room.l_shape_cut_length)), (2.0 * room.half_length) * 0.75)
    cut_wid = min(max(0.0, float(room.l_shape_cut_width)), (2.0 * room.half_width) * 0.75)
    inner_corner: tuple[float, float] | None = None
    if l_corner and cut_len > 1.0 and cut_wid > 1.0:
        if l_corner == "front_left":
            trim_end["left"] = cut_len
            trim_start["front"] = cut_wid
            inner_corner = local_to_world(
                room.center, room.tangent, room.normal, room.half_length - cut_len, room.half_width - cut_wid
            )
        elif l_corner == "front_right":
            trim_end["front"] = cut_wid
            trim_start["right"] = cut_len
            inner_corner = local_to_world(
                room.center, room.tangent, room.normal, room.half_length - cut_len, -room.half_width + cut_wid
            )
        elif l_corner == "back_right":
            trim_end["right"] = cut_len
            trim_start["back"] = cut_wid
            inner_corner = local_to_world(
                room.center, room.tangent, room.normal, -room.half_length + cut_len, -room.half_width + cut_wid
            )
        elif l_corner == "back_left":
            trim_end["back"] = cut_wid
            trim_start["left"] = cut_len
            inner_corner = local_to_world(
                room.center, room.tangent, room.normal, -room.half_length + cut_len, room.half_width - cut_wid
            )
        else:
            l_corner = None

    corner_after_side = {
        "left": "front_left",
        "front": "front_right",
        "right": "back_right",
        "back": "back_left",
    }

    for side, start, end in sides:
        edge = v_sub(end, start)
        edge_len = max(1.0e-6, v_len(edge))
        edge_len_sq = max(1.0e-6, v_dot(edge, edge))
        edge_dir = v_scale(edge, 1.0 / edge_len)

        seg_start_d = max(0.0, min(edge_len, trim_start[side]))
        seg_end_d = max(0.0, min(edge_len, edge_len - trim_end[side]))
        if seg_end_d <= seg_start_d + eps:
            continue

        def point_at(distance: float) -> tuple[float, float]:
            return v_add(start, v_scale(edge_dir, distance))

        seg_start = point_at(seg_start_d)
        seg_end = point_at(seg_end_d)
        append_point(seg_start)

        splits = side_doors.get(side, [])
        if splits:
            entries: list[tuple[float, float]] = []
            for d1, d2 in splits:
                t1 = v_dot(v_sub(d1, start), edge) / edge_len_sq
                t2 = v_dot(v_sub(d2, start), edge) / edge_len_sq
                d1_len = max(0.0, min(edge_len, t1 * edge_len))
                d2_len = max(0.0, min(edge_len, t2 * edge_len))
                lo = max(seg_start_d, min(d1_len, d2_len))
                hi = min(seg_end_d, max(d1_len, d2_len))
                if hi - lo > 1.0e-4:
                    entries.append((lo, hi))

            entries.sort(key=lambda item: item[0])
            merged: list[tuple[float, float]] = []
            for lo, hi in entries:
                if not merged:
                    merged.append((lo, hi))
                    continue
                prev_lo, prev_hi = merged[-1]
                if lo <= prev_hi + 1.0e-4:
                    if hi > prev_hi:
                        merged[-1] = (prev_lo, hi)
                    continue
                merged.append((lo, hi))

            for lo, hi in merged:
                append_point(point_at(lo))
                append_point(point_at(hi))
        else:
            bulge = room.side_bulges.get(side, 0.0)
            if bulge > 0.0:
                mid = point_at((seg_start_d + seg_end_d) * 0.5)
                bulged = v_add(mid, v_scale(room_side_forward(room, side), bulge))
                append_point(bulged)

        append_point(seg_end)
        if inner_corner is not None and l_corner == corner_after_side[side]:
            append_point(inner_corner)

    if len(points) > 1 and v_len(v_sub(points[0], points[-1])) <= eps:
        points.pop()
    return tuple(points)


def corridor_half_width_for_t(theme: ThemeStyle, map_seed: int, corridor_idx: int) -> float:
    base = 96.0 + float(((map_seed + corridor_idx * 31) % 3) * 16)
    if "hell" in theme.corridor_floor.lower():
        base += 8.0
    return base * CORRIDOR_GEOMETRY_SCALE


def corridor_floor_for_distance(
    distance_along: float,
    total_length: float,
    start_floor: int,
    end_floor: int,
    direction: int,
    step_run: float = CORRIDOR_STEP_RUN_UNITS,
) -> int:
    if distance_along < CORRIDOR_END_FLAT_UNITS:
        return int(round(start_floor / float(ELEV_UNIT)) * ELEV_UNIT)
    if (total_length - distance_along) < CORRIDOR_END_FLAT_UNITS:
        return int(round(end_floor / float(ELEV_UNIT)) * ELEV_UNIT)
    inner_len = max(1.0, total_length - (2.0 * CORRIDOR_END_FLAT_UNITS))
    t = (distance_along - CORRIDOR_END_FLAT_UNITS) / inner_len
    t = max(0.0, min(1.0, t))
    base = float(start_floor) + (float(end_floor - start_floor) * t)
    step_index = int((distance_along - CORRIDOR_END_FLAT_UNITS) // step_run) + 1
    level = min(CORRIDOR_MAX_ABS_ELEVATION, step_index * CORRIDOR_STEP_HEIGHT_UNITS)
    target = base + (direction * level)
    return int(round(target / float(ELEV_UNIT)) * ELEV_UNIT)


def enforce_corridor_step_limit(
    levels: list[int],
    fixed_levels: list[int | None],
    max_step: int = 24,
) -> list[int]:
    if not levels:
        return []

    unit = max(1, ELEV_UNIT)
    max_units = max(1, max_step // unit)
    units = [int(round(level / float(unit))) for level in levels]
    fixed = [value is not None for value in fixed_levels]
    fixed_units: list[int | None] = [
        (int(round(value / float(unit))) if value is not None else None)
        for value in fixed_levels
    ]
    for idx, is_fixed in enumerate(fixed):
        if is_fixed and fixed_units[idx] is not None:
            units[idx] = int(fixed_units[idx])

    def relax_pair(i: int, j: int) -> bool:
        a = units[i]
        b = units[j]
        if abs(a - b) <= max_units:
            return False

        if a >= b:
            hi, lo = i, j
        else:
            hi, lo = j, i

        hi_fixed = fixed[hi]
        lo_fixed = fixed[lo]
        high = units[hi]
        low = units[lo]
        changed = False

        if hi_fixed and lo_fixed:
            return False
        if hi_fixed:
            new_low = high - max_units
            if units[lo] != new_low:
                units[lo] = new_low
                changed = True
        elif lo_fixed:
            new_high = low + max_units
            if units[hi] != new_high:
                units[hi] = new_high
                changed = True
        else:
            excess = high - low - max_units
            move_high = (excess + 1) // 2
            move_low = excess // 2
            new_high = high - move_high
            new_low = low + move_low
            if units[hi] != new_high:
                units[hi] = new_high
                changed = True
            if units[lo] != new_low:
                units[lo] = new_low
                changed = True
        return changed

    pair_indices = [(idx, idx + 1) for idx in range(len(units) - 1)]
    for _ in range(max(8, len(units) * 4)):
        changed = False
        for i, j in pair_indices:
            if relax_pair(i, j):
                changed = True
        for i, j in reversed(pair_indices):
            if relax_pair(i, j):
                changed = True
        if not changed:
            break

    # Hard clamp pass to guarantee local walkable deltas after settling.
    for _ in range(max(8, len(units) * 2)):
        changed = False
        for idx in range(1, len(units)):
            if fixed[idx]:
                continue
            low = units[idx - 1] - max_units
            high = units[idx - 1] + max_units
            if units[idx] < low:
                units[idx] = low
                changed = True
            elif units[idx] > high:
                units[idx] = high
                changed = True
        for idx in range(len(units) - 2, -1, -1):
            if fixed[idx]:
                continue
            low = units[idx + 1] - max_units
            high = units[idx + 1] + max_units
            if units[idx] < low:
                units[idx] = low
                changed = True
            elif units[idx] > high:
                units[idx] = high
                changed = True
        if not changed:
            break

    for idx, is_fixed in enumerate(fixed):
        if is_fixed and fixed_units[idx] is not None:
            units[idx] = int(fixed_units[idx])
    return [value * unit for value in units]


def build_corridor_strip(
    start_left: tuple[float, float],
    start_right: tuple[float, float],
    end_left: tuple[float, float],
    end_right: tuple[float, float],
    start_forward: tuple[float, float],
    end_forward: tuple[float, float],
    rng: random.Random,
    core_half_width: float,
    wall_texture: str,
    start_has_door: bool,
    end_has_door: bool,
    start_floor: int,
    end_floor: int,
) -> CorridorStrip:
    start_center = v_mid(start_left, start_right)
    end_center = v_mid(end_left, end_right)
    full_line_vec = v_sub(end_center, start_center)
    full_line_len = max(1.0, v_len(full_line_vec))
    line_dir = v_norm(full_line_vec)
    line_perp = v_perp(line_dir)
    start_forward_n = v_norm(start_forward)
    end_forward_n = v_norm(end_forward)

    start_normal = v_norm(v_sub(start_left, start_right))
    end_normal = v_norm(v_sub(end_left, end_right))
    start_half = 0.5 * v_len(v_sub(start_left, start_right))
    end_half = 0.5 * v_len(v_sub(end_left, end_right))

    start_depth = float(DOOR_THICKNESS) if start_has_door else 0.0
    end_depth = float(DOOR_THICKNESS) if end_has_door else 0.0
    if full_line_len < (start_depth + end_depth + 192.0):
        scale = max(0.0, (full_line_len - 128.0) / max(1.0, (start_depth + end_depth)))
        scale = min(1.0, scale)
        start_depth *= scale
        end_depth *= scale

    inner_start_left = v_add(start_left, v_scale(start_forward_n, start_depth))
    inner_start_right = v_add(start_right, v_scale(start_forward_n, start_depth))
    inner_end_left = v_sub(end_left, v_scale(end_forward_n, end_depth))
    inner_end_right = v_sub(end_right, v_scale(end_forward_n, end_depth))
    start_door_polygon = (
        (start_right, inner_start_right, inner_start_left, start_left)
        if start_depth > 1.0
        else None
    )
    end_door_polygon = (
        (inner_end_right, end_right, end_left, inner_end_left)
        if end_depth > 1.0
        else None
    )

    start_center = v_mid(inner_start_left, inner_start_right)
    end_center = v_mid(inner_end_left, inner_end_right)
    line_vec = v_sub(end_center, start_center)
    line_len = max(1.0, v_len(line_vec))
    line_dir = v_norm(line_vec)
    line_perp = v_perp(line_dir)

    segment_count = max(10, int(line_len / 112.0))
    amplitude = min(220.0, line_len * 0.10)
    if line_len < 420.0:
        amplitude = 0.0
    elif rng.random() < 0.25:
        amplitude = 0.0
    cycles = 1.0 if line_len < 420.0 else rng.choice((1.0, 1.5, 2.0))
    phase = rng.uniform(0.0, math.tau)
    control_len = min(640.0, max(120.0, line_len * 0.33))
    control_len = min(control_len, max(80.0, line_len * 0.45))
    p0 = start_center
    start_control_dir = line_dir if line_len < 420.0 else start_forward_n
    p3 = end_center
    end_control_dir = line_dir if line_len < 420.0 else end_forward_n
    p1 = v_add(p0, v_scale(start_control_dir, control_len))
    p2 = v_sub(p3, v_scale(end_control_dir, control_len))

    sections: list[CorridorSection] = []
    distances: list[float] = [0.0]
    prev_normal = start_normal
    prev_center: tuple[float, float] | None = None
    for idx in range(segment_count + 1):
        t = idx / segment_count
        center = cubic_bezier(p0, p1, p2, p3, t)
        if amplitude > 0.0:
            envelope = math.sin(math.pi * t)
            sway = math.sin((t * cycles * math.tau) + phase) * amplitude * envelope
            center = v_add(center, v_scale(line_perp, sway))

        tangent_vec = cubic_bezier_derivative(p0, p1, p2, p3, t)
        if v_len(tangent_vec) < 1.0e-6:
            tangent_vec = line_vec
        normal = v_perp(v_norm(tangent_vec))
        if v_dot(normal, prev_normal) < 0.0:
            normal = v_scale(normal, -1.0)
        prev_normal = normal
        if t < 0.18:
            half_width = start_half + (core_half_width - start_half) * (t / 0.18)
        elif t > 0.82:
            half_width = core_half_width + (end_half - core_half_width) * ((t - 0.82) / 0.18)
        else:
            half_width = core_half_width

        if idx == 0:
            left = inner_start_left
            right = inner_start_right
            center = start_center
            normal = start_normal
        elif idx == segment_count:
            left = inner_end_left
            right = inner_end_right
            center = end_center
            normal = end_normal
        else:
            left = v_add(center, v_scale(normal, half_width))
            right = v_sub(center, v_scale(normal, half_width))

        sections.append(CorridorSection(left=left, right=right, center=center))
        if prev_center is not None:
            distances.append(distances[-1] + v_len(v_sub(center, prev_center)))
        prev_center = center

    total_length = max(1.0, distances[-1])
    if start_floor == end_floor:
        flat_level = int(round(start_floor / float(ELEV_UNIT)) * ELEV_UNIT)
        floors = [flat_level for _ in range(segment_count)]
    else:
        stair_direction = 1 if end_floor > start_floor else -1
        floors: list[int] = []
        fixed_levels: list[int | None] = []
        for idx in range(segment_count):
            mid_dist = 0.5 * (distances[idx] + distances[idx + 1])
            floors.append(
                corridor_floor_for_distance(
                    mid_dist,
                    total_length,
                    start_floor,
                    end_floor,
                    stair_direction,
                )
            )
            if mid_dist < CORRIDOR_END_FLAT_UNITS:
                fixed_levels.append(start_floor)
            elif (total_length - mid_dist) < CORRIDOR_END_FLAT_UNITS:
                fixed_levels.append(end_floor)
            else:
                fixed_levels.append(None)

        floors = enforce_corridor_step_limit(floors, fixed_levels, max_step=CORRIDOR_MAX_ADJ_STEP)

    return CorridorStrip(
        sections=tuple(sections),
        floors=tuple(floors),
        wall_texture=wall_texture,
        start_door_polygon=start_door_polygon,
        end_door_polygon=end_door_polygon,
    )


def build_key_lock_plan(
    room_count: int,
    edges: list[tuple[int, int]],
) -> tuple[list[tuple[int, str]], list[tuple[int, int, str]]]:
    if room_count <= 1:
        return [], []

    adjacency: list[list[int]] = [[] for _ in range(room_count)]
    edge_index: dict[frozenset[int], int] = {}
    for idx, (a, b) in enumerate(edges):
        adjacency[a].append(b)
        adjacency[b].append(a)
        edge_index[frozenset((a, b))] = idx

    # Explicit 8/9-room flow:
    # START(0) -> branch(1, blue door) -> branch(3, yellow door) -> branch(5, red door) -> EXIT room(7)
    # side dead-ends with keys: 2(blue), 4(yellow), 6(red)
    # Lock room index points to the BRANCH-side endpoint where the colored door sits.
    required_edges = (
        frozenset((0, 1)),
        frozenset((1, 2)),
        frozenset((1, 3)),
        frozenset((3, 4)),
        frozenset((3, 5)),
        frozenset((5, 6)),
        frozenset((5, 7)),
    )
    if room_count in {8, 9} and all(edge in edge_index for edge in required_edges):
        key_sequence = [(2, "blue"), (4, "yellow"), (6, "red")]
        lock_sequence = [
            (edge_index[frozenset((1, 3))], 1, "blue"),
            (edge_index[frozenset((3, 5))], 3, "yellow"),
            (edge_index[frozenset((5, 7))], 5, "red"),
        ]
        return key_sequence, lock_sequence

    # Strict 10-room flow:
    # same core lock/key rooms + one passage room (8) spliced into one core segment
    # and one extra dead-end room (9) attached to a lock-room parent (1/3/5).
    if room_count == 10:
        key_edges = (
            frozenset((1, 2)),
            frozenset((3, 4)),
            frozenset((5, 6)),
        )
        if all(edge in edge_index for edge in key_edges):
            key_sequence = [(2, "blue"), (4, "yellow"), (6, "red")]

            def pick_lock_edge(
                candidates: tuple[tuple[int, int], ...],
                lock_room: int,
                color: str,
            ) -> tuple[int, int, str] | None:
                for a, b in candidates:
                    key = frozenset((a, b))
                    if key in edge_index:
                        return (edge_index[key], lock_room, color)
                return None

            blue_lock = pick_lock_edge(((1, 3), (1, 8)), 1, "blue")
            yellow_lock = pick_lock_edge(((3, 5), (3, 8)), 3, "yellow")
            red_lock = pick_lock_edge(((5, 7), (5, 8)), 5, "red")
            if blue_lock and yellow_lock and red_lock:
                return key_sequence, [blue_lock, yellow_lock, red_lock]

    parent = [-1 for _ in range(room_count)]
    depth = [10**9 for _ in range(room_count)]
    queue: deque[int] = deque([0])
    depth[0] = 0
    while queue:
        node = queue.popleft()
        for nxt in adjacency[node]:
            if depth[nxt] <= depth[node] + 1:
                continue
            depth[nxt] = depth[node] + 1
            parent[nxt] = node
            queue.append(nxt)

    dead_ends = [idx for idx in range(1, room_count) if len(adjacency[idx]) == 1 and depth[idx] < 10**9]
    dead_ends.sort(key=lambda idx: (depth[idx], idx))
    key_colors = ("blue", "yellow", "red")
    key_sequence = [(room_idx, key_colors[i]) for i, room_idx in enumerate(dead_ends[:len(key_colors)])]

    lock_sequence: list[tuple[int, int, str]] = []
    if len(key_sequence) >= 2:
        yellow_room = key_sequence[1][0]
        yellow_parent = parent[yellow_room]
        if yellow_parent >= 0:
            lock_sequence.append((edge_index[frozenset((yellow_room, yellow_parent))], yellow_parent, "blue"))
    if len(key_sequence) >= 3:
        red_room = key_sequence[2][0]
        red_parent = parent[red_room]
        if red_parent >= 0:
            lock_sequence.append((edge_index[frozenset((red_room, red_parent))], red_parent, "yellow"))

    # Gate a late branch with the red key so progression becomes:
    # START -> BLUE KEY -> BLUE DOOR -> YELLOW KEY -> YELLOW DOOR -> RED KEY -> RED DOOR -> EXIT.
    if len(key_sequence) >= 3:
        key_rooms = {room_idx for room_idx, _color in key_sequence}
        red_room = key_sequence[2][0]
        late_candidates = [
            idx
            for idx in dead_ends
            if idx not in key_rooms and depth[idx] > depth[red_room]
        ]
        if not late_candidates:
            late_candidates = [
                idx
                for idx in range(1, room_count)
                if idx not in key_rooms and depth[idx] < 10**9
            ]
        if late_candidates:
            target = max(late_candidates, key=lambda idx: (depth[idx], idx))
            target_parent = parent[target]
            if target_parent >= 0:
                lock_sequence.append((edge_index[frozenset((target, target_parent))], target_parent, "red"))

    return key_sequence, lock_sequence


def generate_poly_layout(
    spec: EpisodeMapSpec,
    theme: ThemeStyle,
    rng: random.Random,
) -> PolyLayout:
    room_count = max(8, spec.room_target)
    centers, edges = generate_room_graph(room_count, rng)
    room_templates: list[tuple[float, float, dict[str, float], str | None, float, float]] = []
    room_half_sizes: list[tuple[float, float]] = []
    for idx in range(len(centers)):
        half_length = rng.uniform(260.0, 690.0) * ROOM_GEOMETRY_SCALE
        half_width = rng.uniform(180.0, 480.0) * ROOM_GEOMETRY_SCALE
        shape_rng = random.Random((spec.map_seed * 334214467 + idx * 2654435761) & 0xFFFFFFFF)
        l_shape_corner: str | None = None
        l_shape_cut_length = 0.0
        l_shape_cut_width = 0.0
        if shape_rng.random() < ROOM_L_SHAPE_CHANCE:
            l_shape_corner = shape_rng.choice(("front_left", "front_right", "back_left", "back_right"))
            l_shape_cut_length = shape_rng.uniform(half_length * 0.33, half_length * 0.66)
            l_shape_cut_width = shape_rng.uniform(half_width * 0.33, half_width * 0.66)

        side_bulges: dict[str, float] = {}
        if l_shape_corner is None:
            for side in ("front", "back", "left", "right"):
                if shape_rng.random() < 0.35:
                    side_bulges[side] = shape_rng.uniform(24.0, 96.0) * ROOM_GEOMETRY_SCALE
        room_templates.append(
            (
                half_length,
                half_width,
                side_bulges,
                l_shape_corner,
                l_shape_cut_length,
                l_shape_cut_width,
            )
        )
        room_half_sizes.append((half_length, half_width))

    centers = relax_room_centers_for_corridor_clearance(centers, edges, room_half_sizes)
    centers = relax_room_centers_for_corridor_room_intersections(centers, edges, room_templates)
    room_floor_by_index = assign_room_floor_heights(room_count, edges, centers, rng)
    tangents = compute_room_tangents_from_graph(centers, edges)

    rooms: list[OrientedRoom] = []
    for idx, center in enumerate(centers):
        (
            half_length,
            half_width,
            side_bulges,
            l_shape_corner,
            l_shape_cut_length,
            l_shape_cut_width,
        ) = room_templates[idx]
        log_trace(
            f"ROOM_GEOMETRY_ATTEMPT idx={idx} center=({center[0]:.1f},{center[1]:.1f}) "
            f"half_length={half_length:.1f} half_width={half_width:.1f} "
            f"l_corner={l_shape_corner} l_cut_len={l_shape_cut_length:.1f} l_cut_wid={l_shape_cut_width:.1f}"
        )
        room = build_oriented_room(
            center,
            tangents[idx],
            half_length,
            half_width,
            side_bulges=dict(side_bulges),
            l_shape_corner=l_shape_corner,
            l_shape_cut_length=l_shape_cut_length,
            l_shape_cut_width=l_shape_cut_width,
        )
        rooms.append(room)
        log_trace(
            f"ROOM_GEOMETRY_ACCEPT idx={idx} center=({room.center[0]:.1f},{room.center[1]:.1f}) "
            f"half_length={room.half_length:.1f} half_width={room.half_width:.1f}"
        )
    room_bboxes: list[tuple[float, float, float, float]] = []
    room_bbox_margin = 64.0
    for room in rooms:
        xs = [p[0] for p in room.polygon]
        ys = [p[1] for p in room.polygon]
        room_bboxes.append((min(xs), max(xs), min(ys), max(ys)))

    def expanded_room_bbox(room_idx: int) -> tuple[float, float, float, float]:
        minx, maxx, miny, maxy = room_bboxes[room_idx]
        return (
            minx - room_bbox_margin,
            maxx + room_bbox_margin,
            miny - room_bbox_margin,
            maxy + room_bbox_margin,
        )

    def point_in_bbox(
        point: tuple[float, float],
        bbox: tuple[float, float, float, float],
    ) -> bool:
        minx, maxx, miny, maxy = bbox
        x, y = point
        return minx <= x <= maxx and miny <= y <= maxy

    def segment_hits_bbox(
        a: tuple[float, float],
        b: tuple[float, float],
        bbox: tuple[float, float, float, float],
    ) -> bool:
        if point_in_bbox(a, bbox) or point_in_bbox(b, bbox):
            return True
        minx, maxx, miny, maxy = bbox
        edges = (
            ((minx, miny), (maxx, miny)),
            ((maxx, miny), (maxx, maxy)),
            ((maxx, maxy), (minx, maxy)),
            ((minx, maxy), (minx, miny)),
        )
        for edge_a, edge_b in edges:
            if segment_to_segment_distance_sq(a, b, edge_a, edge_b) <= 1e-6:
                return True
        return False

    def as_point(obj: object) -> tuple[float, float] | None:
        if (
            isinstance(obj, (tuple, list))
            and len(obj) == 2
            and isinstance(obj[0], (int, float))
            and isinstance(obj[1], (int, float))
        ):
            return (float(obj[0]), float(obj[1]))
        return None

    def collect_corridor_geometry(
        data: object,
    ) -> tuple[list[tuple[float, float]], list[tuple[tuple[float, float], tuple[float, float]]]]:
        points: list[tuple[float, float]] = []
        segments: list[tuple[tuple[float, float], tuple[float, float]]] = []

        point = as_point(data)
        if point is not None:
            points.append(point)
            return points, segments

        if not isinstance(data, (tuple, list)):
            return points, segments

        direct_points: list[tuple[float, float]] = []
        for item in data:
            direct_point = as_point(item)
            if direct_point is not None:
                direct_points.append(direct_point)
                continue
            sub_points, sub_segments = collect_corridor_geometry(item)
            points.extend(sub_points)
            segments.extend(sub_segments)

        points.extend(direct_points)
        if len(direct_points) >= 2:
            for i in range(len(direct_points) - 1):
                segments.append((direct_points[i], direct_points[i + 1]))
            if len(direct_points) >= 3:
                segments.append((direct_points[-1], direct_points[0]))

        return points, segments

    def polygons_overlap(
        poly_a: tuple[tuple[float, float], ...],
        poly_b: tuple[tuple[float, float], ...],
    ) -> bool:
        if len(poly_a) < 3 or len(poly_b) < 3:
            return False
        bbox_a = local_poly_bbox(list(poly_a))
        bbox_b = local_poly_bbox(list(poly_b))
        if not boxes_intersect(bbox_a, bbox_b):
            return False
        if min_edge_distance_between_polygons_sq(poly_a, poly_b) <= 1.0e-6:
            return True
        if point_in_polygon(poly_a[0], poly_b):
            return True
        if point_in_polygon(poly_b[0], poly_a):
            return True
        return False
    room_walls = [
        texture_from_palette(
            theme.room_wall_textures,
            spec.map_seed + idx * 7,
            theme.room_wall_textures[0],
        )
        for idx in range(len(rooms))
    ]
    adjacency: list[list[int]] = [[] for _ in range(len(rooms))]
    for a, b in edges:
        if 0 <= a < len(adjacency) and 0 <= b < len(adjacency):
            adjacency[a].append(b)
            adjacency[b].append(a)
    depth = [10**9 for _ in range(len(rooms))]
    parent = [-1 for _ in range(len(rooms))]
    queue: deque[int] = deque([0])
    depth[0] = 0
    while queue:
        node = queue.popleft()
        for nxt in adjacency[node]:
            if depth[nxt] <= depth[node] + 1:
                continue
            depth[nxt] = depth[node] + 1
            parent[nxt] = node
            queue.append(nxt)

    def corridor_edge_step_capacity(
        start_open_seg: tuple[tuple[float, float], tuple[float, float]],
        end_open_seg: tuple[tuple[float, float], tuple[float, float]],
    ) -> int:
        s_mid = v_mid(start_open_seg[0], start_open_seg[1])
        e_mid = v_mid(end_open_seg[0], end_open_seg[1])
        line_len = max(1.0, v_len(v_sub(e_mid, s_mid)))
        segment_count = max(10, int(line_len / 112.0))
        fixed_start = 0
        fixed_end = 0
        for seg_idx in range(segment_count):
            t0 = seg_idx / segment_count
            t1 = (seg_idx + 1) / segment_count
            mid = ((t0 + t1) * 0.5) * line_len
            if mid < CORRIDOR_END_FLAT_UNITS:
                fixed_start += 1
            if (line_len - mid) < CORRIDOR_END_FLAT_UNITS:
                fixed_end += 1
        start_last = max(0, fixed_start - 1)
        end_first = min(segment_count - 1, segment_count - fixed_end)
        transitions = max(1, end_first - start_last)
        return max(CORRIDOR_MAX_ADJ_STEP, transitions * CORRIDOR_MAX_ADJ_STEP)

    key_sequence, lock_sequence = build_key_lock_plan(len(rooms), edges)
    locked_endpoints = {(edge_idx, room_idx): color for edge_idx, room_idx, color in lock_sequence}

    room_side_doors: list[dict[str, list[tuple[tuple[float, float], tuple[float, float]]]]] = [{} for _ in rooms]
    # Keep geometry RNG sequence stable: room-light randomization uses a
    # dedicated deterministic stream derived from the map seed.
    room_light_rng = random.Random((int(spec.map_seed) ^ 0x5A17C0DE) & 0xFFFFFFFF)
    room_light_by_index: list[int] = [random_room_light(theme.room_light, room_light_rng) for _ in rooms]
    path_sector_plans: list[SectorPlan] = []
    corridors: list[CorridorStrip] = []
    used_sides: list[set[str]] = [set() for _ in rooms]
    for idx, (room_a_idx, room_b_idx) in enumerate(edges):
        room_a = rooms[room_a_idx]
        room_b = rooms[room_b_idx]
        line_dir = v_norm(v_sub(room_b.center, room_a.center))
        side_a = choose_room_side(room_a, line_dir, used_sides[room_a_idx])
        used_sides[room_a_idx].add(side_a)
        side_b = choose_room_side(room_b, v_scale(line_dir, -1.0), used_sides[room_b_idx])
        used_sides[room_b_idx].add(side_b)

        raw_start = door_segment_on_side(room_a, side_a, float(DOOR_NATIVE_WIDTH), rng)
        raw_end = door_segment_on_side(room_b, side_b, float(DOOR_NATIVE_WIDTH), rng)
        start_outward = room_side_forward(room_a, side_a)
        end_outward = room_side_forward(room_b, side_b)
        start_recess = build_recess_endpoint(raw_start, start_outward)
        end_recess = build_recess_endpoint(raw_end, end_outward)
        room_side_doors[room_a_idx].setdefault(side_a, []).append(start_recess["wall_open"])  # type: ignore[arg-type]
        room_side_doors[room_b_idx].setdefault(side_b, []).append(end_recess["wall_open"])  # type: ignore[arg-type]

        start_forward = start_outward
        end_forward = v_scale(end_outward, -1.0)
        start_open = start_recess["corridor_open"]  # type: ignore[assignment]
        end_open = end_recess["corridor_open"]  # type: ignore[assignment]

        if depth[room_a_idx] <= depth[room_b_idx]:
            parent_idx, child_idx = room_a_idx, room_b_idx
        else:
            parent_idx, child_idx = room_b_idx, room_a_idx
        edge_cap = corridor_edge_step_capacity(start_open, end_open)
        pf = int(room_floor_by_index[parent_idx])
        cf = int(room_floor_by_index[child_idx])
        if abs(cf - pf) > edge_cap:
            clamped = pf + (edge_cap if cf > pf else -edge_cap)
            clamped = int(round(clamped / 8.0) * 8)
            clamped = max(-ROOM_FLOOR_VARIATION_MAX, min(ROOM_FLOOR_VARIATION_MAX, clamped))
            room_floor_by_index[child_idx] = clamped

        start_left, start_right = orient_segment_for_direction(start_open[0], start_open[1], start_forward)
        end_left, end_right = orient_segment_for_direction(end_open[0], end_open[1], end_forward)
        start_has_door = rng.random() < 0.65
        end_has_door = rng.random() < 0.65
        start_lock_color = locked_endpoints.get((idx, room_a_idx), "")
        end_lock_color = locked_endpoints.get((idx, room_b_idx), "")
        if start_lock_color:
            start_has_door = True
        elif start_has_door and rng.random() < NON_COLORED_DOOR_REMOVAL_CHANCE:
            start_has_door = False
        if end_lock_color:
            end_has_door = True
        elif end_has_door and rng.random() < NON_COLORED_DOOR_REMOVAL_CHANCE:
            end_has_door = False
        if room_a_idx == 0 and idx == 0 and not start_has_door and not end_has_door:
            start_has_door = True
        wall_tex = texture_from_palette(
            theme.corridor_wall_textures,
            spec.map_seed + idx * 17,
            theme.corridor_wall_textures[0],
        )
        corridor_light_level = random_corridor_light(theme.corridor_light, rng)
        strip = build_corridor_strip(
            start_left=start_left,
            start_right=start_right,
            end_left=end_left,
            end_right=end_right,
            start_forward=start_forward,
            end_forward=end_forward,
            rng=rng,
            core_half_width=corridor_half_width_for_t(theme, spec.map_seed, idx),
            wall_texture=wall_tex,
            start_has_door=False,
            end_has_door=False,
            start_floor=int(room_floor_by_index[room_a_idx]),
            end_floor=int(room_floor_by_index[room_b_idx]),
        )
        corridors.append(strip)

        # Corridor safety guard:
        # corridor vertices must not land inside bbox of unrelated rooms.
        corridor_vertices: list[tuple[float, float]] = []
        corridor_segments: list[tuple[tuple[float, float], tuple[float, float]]] = []
        strip_quads: list[tuple[tuple[float, float], ...]] = []
        for sec in strip.sections:
            corridor_vertices.append((float(sec.center[0]), float(sec.center[1])))
            corridor_vertices.append((float(sec.left[0]), float(sec.left[1])))
            corridor_vertices.append((float(sec.right[0]), float(sec.right[1])))
            corridor_segments.append(
                ((float(sec.left[0]), float(sec.left[1])), (float(sec.right[0]), float(sec.right[1])))
            )
        for sec_prev, sec_next in zip(strip.sections, strip.sections[1:]):
            corridor_segments.append(
                (
                    (float(sec_prev.center[0]), float(sec_prev.center[1])),
                    (float(sec_next.center[0]), float(sec_next.center[1])),
                )
            )
            corridor_segments.append(
                (
                    (float(sec_prev.left[0]), float(sec_prev.left[1])),
                    (float(sec_next.left[0]), float(sec_next.left[1])),
                )
            )
            corridor_segments.append(
                (
                    (float(sec_prev.right[0]), float(sec_prev.right[1])),
                    (float(sec_next.right[0]), float(sec_next.right[1])),
                )
            )
            strip_quads.append(
                (
                    (float(sec_prev.left[0]), float(sec_prev.left[1])),
                    (float(sec_next.left[0]), float(sec_next.left[1])),
                    (float(sec_next.right[0]), float(sec_next.right[1])),
                    (float(sec_prev.right[0]), float(sec_prev.right[1])),
                )
            )
        for recess in (start_recess, end_recess):
            for value in recess.values():
                points, segments = collect_corridor_geometry(value)
                corridor_vertices.extend(points)
                corridor_segments.extend(segments)

        for room_idx in range(len(rooms)):
            if room_idx in {room_a_idx, room_b_idx}:
                continue
            bbox = expanded_room_bbox(room_idx)
            for point in corridor_vertices:
                if point_in_bbox(point, bbox):
                    raise ValueError(
                        f"CORRIDOR_BBOX_CONFLICT map={spec.output_map} edge={idx} "
                        f"rooms=({room_a_idx},{room_b_idx}) hit_room={room_idx} "
                        f"point=({point[0]:.2f},{point[1]:.2f})"
                    )
            for seg_a, seg_b in corridor_segments:
                if segment_hits_bbox(seg_a, seg_b, bbox):
                    raise ValueError(
                        f"CORRIDOR_BBOX_CONFLICT map={spec.output_map} edge={idx} "
                        f"rooms=({room_a_idx},{room_b_idx}) hit_room={room_idx} "
                        f"segment=({seg_a[0]:.2f},{seg_a[1]:.2f})->({seg_b[0]:.2f},{seg_b[1]:.2f})"
                    )

        # Endpoint penetration diagnostic:
        # corridor body must not overlap the source/target room interior
        # except the immediate doorway-adjacent quad.
        room_a_poly = tuple((float(p[0]), float(p[1])) for p in rooms[room_a_idx].polygon)
        room_b_poly = tuple((float(p[0]), float(p[1])) for p in rooms[room_b_idx].polygon)
        quad_count = len(strip_quads)
        for quad_idx, quad in enumerate(strip_quads):
            if quad_idx >= 1 and polygons_overlap(quad, room_a_poly):
                raise ValueError(
                    f"CORRIDOR_BBOX_CONFLICT map={spec.output_map} edge={idx} "
                    f"rooms=({room_a_idx},{room_b_idx}) hit_room={room_a_idx} "
                    f"endpoint_penetration=source quad={quad_idx}/{quad_count}"
                )
            if quad_idx <= max(0, quad_count - 2) and polygons_overlap(quad, room_b_poly):
                raise ValueError(
                    f"CORRIDOR_BBOX_CONFLICT map={spec.output_map} edge={idx} "
                    f"rooms=({room_a_idx},{room_b_idx}) hit_room={room_b_idx} "
                    f"endpoint_penetration=target quad={quad_idx}/{quad_count}"
                )

        if start_has_door:
            start_floor = room_floor_by_index[room_a_idx]
            start_lintel_ceiling = start_floor + ROOM_CEILING_CLEARANCE - DOOR_LINTEL_CEILING_DROP_UNITS
            start_room_light = room_light_by_index[room_a_idx]
            start_marker_tex = LOCK_FRAME_TEXTURE_BY_COLOR.get(start_lock_color, "")
            start_room_marker_tex = start_marker_tex or room_walls[room_a_idx]
            start_corr_marker_tex = start_marker_tex or wall_tex
            path_sector_plans.append(
                SectorPlan(
                    polygon=start_recess["inner_poly"],  # type: ignore[arg-type]
                    floor_height=start_floor,
                    ceiling_height=start_floor + ROOM_CEILING_CLEARANCE,
                    floor_texture=theme.room_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=start_room_light,
                    wall_texture=room_walls[room_a_idx],
                    kind="transition",
                )
            )
            path_sector_plans.append(
                SectorPlan(
                    polygon=start_recess["micro_lintel_poly"],  # type: ignore[arg-type]
                    floor_height=start_floor,
                    ceiling_height=start_lintel_ceiling,
                    floor_texture=theme.room_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=start_room_light,
                    wall_texture=room_walls[room_a_idx],
                    kind="lintel_room",
                )
            )
            path_sector_plans.append(
                SectorPlan(
                    polygon=start_recess["door_poly"],  # type: ignore[arg-type]
                    floor_height=start_floor,
                    ceiling_height=start_floor,
                    floor_texture=theme.corridor_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=corridor_light_level,
                    wall_texture=theme.door_texture,
                    kind="door",
                    door_edge=idx,
                    door_room=room_a_idx,
                )
            )
            path_sector_plans.append(
                SectorPlan(
                    polygon=start_recess["side_left_marker_poly"],  # type: ignore[arg-type]
                    floor_height=start_floor,
                    ceiling_height=start_lintel_ceiling,
                    floor_texture=theme.corridor_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=start_room_light,
                    wall_texture=start_room_marker_tex,
                    kind="door_gap_room",
                )
            )
            path_sector_plans.append(
                SectorPlan(
                    polygon=start_recess["side_left_marker_back_poly"],  # type: ignore[arg-type]
                    floor_height=start_floor,
                    ceiling_height=start_lintel_ceiling,
                    floor_texture=theme.corridor_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=corridor_light_level,
                    wall_texture=start_corr_marker_tex,
                    kind="door_gap_corridor",
                )
            )
            path_sector_plans.append(
                SectorPlan(
                    polygon=start_recess["side_right_marker_back_poly"],  # type: ignore[arg-type]
                    floor_height=start_floor,
                    ceiling_height=start_lintel_ceiling,
                    floor_texture=theme.corridor_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=corridor_light_level,
                    wall_texture=start_corr_marker_tex,
                    kind="door_gap_corridor",
                )
            )
            path_sector_plans.append(
                SectorPlan(
                    polygon=start_recess["side_right_marker_poly"],  # type: ignore[arg-type]
                    floor_height=start_floor,
                    ceiling_height=start_lintel_ceiling,
                    floor_texture=theme.corridor_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=start_room_light,
                    wall_texture=start_room_marker_tex,
                    kind="door_gap_room",
                )
            )
            path_sector_plans.append(
                SectorPlan(
                    polygon=start_recess["micro_lintel_back_poly"],  # type: ignore[arg-type]
                    floor_height=start_floor,
                    ceiling_height=start_lintel_ceiling,
                    floor_texture=theme.corridor_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=corridor_light_level,
                    wall_texture=wall_tex,
                    kind="lintel_corridor",
                )
            )
            path_sector_plans.append(
                SectorPlan(
                    polygon=start_recess["outer_poly"],  # type: ignore[arg-type]
                    floor_height=start_floor,
                    ceiling_height=start_floor + ROOM_CEILING_CLEARANCE,
                    floor_texture=theme.corridor_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=corridor_light_level,
                    wall_texture=wall_tex,
                    kind="transition",
                )
            )
        else:
            start_open_light = int(round((room_light_by_index[room_a_idx] + corridor_light_level) * 0.5))
            path_sector_plans.append(
                SectorPlan(
                    polygon=start_recess["open_poly"],  # type: ignore[arg-type]
                    floor_height=room_floor_by_index[room_a_idx],
                    ceiling_height=room_floor_by_index[room_a_idx] + ROOM_CEILING_CLEARANCE,
                    floor_texture=theme.transition_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=start_open_light,
                    wall_texture=theme.transition_wall_textures[0],
                    kind="transition",
                )
            )

        if end_has_door:
            end_floor = room_floor_by_index[room_b_idx]
            end_lintel_ceiling = end_floor + ROOM_CEILING_CLEARANCE - DOOR_LINTEL_CEILING_DROP_UNITS
            end_room_light = room_light_by_index[room_b_idx]
            end_marker_tex = LOCK_FRAME_TEXTURE_BY_COLOR.get(end_lock_color, "")
            end_room_marker_tex = end_marker_tex or room_walls[room_b_idx]
            end_corr_marker_tex = end_marker_tex or wall_tex
            path_sector_plans.append(
                SectorPlan(
                    polygon=end_recess["inner_poly"],  # type: ignore[arg-type]
                    floor_height=end_floor,
                    ceiling_height=end_floor + ROOM_CEILING_CLEARANCE,
                    floor_texture=theme.room_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=end_room_light,
                    wall_texture=room_walls[room_b_idx],
                    kind="transition",
                )
            )
            path_sector_plans.append(
                SectorPlan(
                    polygon=end_recess["micro_lintel_poly"],  # type: ignore[arg-type]
                    floor_height=end_floor,
                    ceiling_height=end_lintel_ceiling,
                    floor_texture=theme.room_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=end_room_light,
                    wall_texture=room_walls[room_b_idx],
                    kind="lintel_room",
                )
            )
            path_sector_plans.append(
                SectorPlan(
                    polygon=end_recess["door_poly"],  # type: ignore[arg-type]
                    floor_height=end_floor,
                    ceiling_height=end_floor,
                    floor_texture=theme.corridor_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=corridor_light_level,
                    wall_texture=theme.door_texture,
                    kind="door",
                    door_edge=idx,
                    door_room=room_b_idx,
                )
            )
            path_sector_plans.append(
                SectorPlan(
                    polygon=end_recess["side_left_marker_poly"],  # type: ignore[arg-type]
                    floor_height=end_floor,
                    ceiling_height=end_lintel_ceiling,
                    floor_texture=theme.corridor_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=end_room_light,
                    wall_texture=end_room_marker_tex,
                    kind="door_gap_room",
                )
            )
            path_sector_plans.append(
                SectorPlan(
                    polygon=end_recess["side_left_marker_back_poly"],  # type: ignore[arg-type]
                    floor_height=end_floor,
                    ceiling_height=end_lintel_ceiling,
                    floor_texture=theme.corridor_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=corridor_light_level,
                    wall_texture=end_corr_marker_tex,
                    kind="door_gap_corridor",
                )
            )
            path_sector_plans.append(
                SectorPlan(
                    polygon=end_recess["side_right_marker_back_poly"],  # type: ignore[arg-type]
                    floor_height=end_floor,
                    ceiling_height=end_lintel_ceiling,
                    floor_texture=theme.corridor_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=corridor_light_level,
                    wall_texture=end_corr_marker_tex,
                    kind="door_gap_corridor",
                )
            )
            path_sector_plans.append(
                SectorPlan(
                    polygon=end_recess["side_right_marker_poly"],  # type: ignore[arg-type]
                    floor_height=end_floor,
                    ceiling_height=end_lintel_ceiling,
                    floor_texture=theme.corridor_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=end_room_light,
                    wall_texture=end_room_marker_tex,
                    kind="door_gap_room",
                )
            )
            path_sector_plans.append(
                SectorPlan(
                    polygon=end_recess["micro_lintel_back_poly"],  # type: ignore[arg-type]
                    floor_height=end_floor,
                    ceiling_height=end_lintel_ceiling,
                    floor_texture=theme.corridor_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=corridor_light_level,
                    wall_texture=wall_tex,
                    kind="lintel_corridor",
                )
            )
            path_sector_plans.append(
                SectorPlan(
                    polygon=end_recess["outer_poly"],  # type: ignore[arg-type]
                    floor_height=end_floor,
                    ceiling_height=end_floor + ROOM_CEILING_CLEARANCE,
                    floor_texture=theme.corridor_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=corridor_light_level,
                    wall_texture=wall_tex,
                    kind="transition",
                )
            )
        else:
            end_open_light = int(round((room_light_by_index[room_b_idx] + corridor_light_level) * 0.5))
            path_sector_plans.append(
                SectorPlan(
                    polygon=end_recess["open_poly"],  # type: ignore[arg-type]
                    floor_height=room_floor_by_index[room_b_idx],
                    ceiling_height=room_floor_by_index[room_b_idx] + ROOM_CEILING_CLEARANCE,
                    floor_texture=theme.transition_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=end_open_light,
                    wall_texture=theme.transition_wall_textures[0],
                    kind="transition",
                )
            )

        for seg_idx, floor_height in enumerate(strip.floors):
            a = strip.sections[seg_idx]
            b = strip.sections[seg_idx + 1]
            polygon = (a.right, b.right, b.left, a.left)
            path_sector_plans.append(
                SectorPlan(
                    polygon=polygon,
                    floor_height=floor_height,
                    ceiling_height=floor_height + ROOM_CEILING_CLEARANCE,
                    floor_texture=theme.corridor_floor,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=corridor_light_level,
                    wall_texture=strip.wall_texture,
                    kind="corridor",
                )
            )

    room_sector_plans: list[SectorPlan] = []
    for idx, room in enumerate(rooms):
        room_sector_plans.append(
            SectorPlan(
                polygon=room_polygon_with_door_splits(room, room_side_doors[idx]),
                floor_height=room_floor_by_index[idx],
                ceiling_height=room_floor_by_index[idx] + ROOM_CEILING_CLEARANCE,
                floor_texture=theme.room_floor,
                ceiling_texture=theme.ceiling_flat,
                light_level=room_light_by_index[idx],
                wall_texture=room_walls[idx],
                kind="room",
            )
        )

    return PolyLayout(
        rooms=rooms,
        corridors=corridors,
        sector_plans=room_sector_plans + path_sector_plans,
        connections=edges,
        key_sequence=key_sequence,
        lock_sequence=lock_sequence,
        room_door_sides=tuple(tuple(sorted(doors.keys())) for doors in room_side_doors),
    )


def signed_area(points: list[tuple[int, int]]) -> float:
    area2 = 0.0
    for idx in range(len(points)):
        x1, y1 = points[idx]
        x2, y2 = points[(idx + 1) % len(points)]
        area2 += (x1 * y2) - (x2 * y1)
    return area2 * 0.5


def simplify_polygon(points: list[tuple[int, int]]) -> list[tuple[int, int]]:
    cleaned: list[tuple[int, int]] = []
    for point in points:
        if cleaned and point == cleaned[-1]:
            continue
        cleaned.append(point)
    while len(cleaned) > 1 and cleaned[0] == cleaned[-1]:
        cleaned.pop()
    return cleaned


def collapse_short_polygon_edges(
    points: list[tuple[int, int]],
    min_edge_units: float,
) -> list[tuple[int, int]]:
    if len(points) < 3:
        return points
    min_edge_sq = float(min_edge_units) * float(min_edge_units)
    collapsed = list(points)
    changed = True
    while changed and len(collapsed) > 3:
        changed = False
        n = len(collapsed)
        for idx in range(n):
            a = collapsed[idx]
            b_idx = (idx + 1) % n
            b = collapsed[b_idx]
            dx = float(b[0] - a[0])
            dy = float(b[1] - a[1])
            if (dx * dx) + (dy * dy) >= min_edge_sq:
                continue
            del collapsed[b_idx]
            changed = True
            break
        if changed:
            collapsed = simplify_polygon(collapsed)
    if len(collapsed) < 3:
        return []
    if signed_area(collapsed) > 0.0:
        collapsed.reverse()
    return collapsed


def normalize_plan_polygon(polygon: tuple[tuple[float, float], ...]) -> list[tuple[int, int]]:
    rounded = [(int(round(x)), int(round(y))) for x, y in polygon]
    cleaned = simplify_polygon(rounded)
    if len(cleaned) < 3:
        return []
    if signed_area(cleaned) > 0.0:
        cleaned.reverse()
    return cleaned


def poly_layout_to_map(
    layout: PolyLayout,
    map_name: str,
    door_texture: str,
) -> tuple[MutableMap, dict[int, set[int]], dict[tuple[int, int], int], dict[int, int]]:
    map_data = MutableMap(name=map_name)
    vertex_lookup: dict[tuple[int, int], int] = {}
    sector_kind: dict[int, str] = {}
    door_lines_by_sector: dict[int, set[int]] = {}
    door_sector_by_endpoint: dict[tuple[int, int], int] = {}
    room_sector_by_room_index: dict[int, int] = {}

    def vertex_index(point: tuple[int, int]) -> int:
        if point in vertex_lookup:
            return vertex_lookup[point]
        map_data.vertices.append(Vertex(point[0], point[1]))
        idx = len(map_data.vertices) - 1
        vertex_lookup[point] = idx
        return idx

    edge_occurrences: dict[tuple[int, int], list[tuple[int, int, int, str]]] = {}
    door_face_min_len_sq = int((DOOR_NATIVE_WIDTH * 0.60) ** 2)
    lintel_kinds = {"lintel_room", "lintel_corridor"}
    door_gap_kinds = {"door_gap", "door_gap_room", "door_gap_corridor"}

    for plan in layout.sector_plans:
        polygon = normalize_plan_polygon(plan.polygon)
        if len(polygon) < 3:
            continue
        sector_idx = add_sector(
            map_data,
            floor_height=plan.floor_height,
            ceiling_height=plan.ceiling_height,
            floor_texture=plan.floor_texture,
            ceiling_texture=plan.ceiling_texture,
            light_level=plan.light_level,
        )
        sector_kind[sector_idx] = plan.kind
        if plan.kind == "room":
            room_sector_by_room_index[len(room_sector_by_room_index)] = sector_idx
        if plan.kind == "door" and plan.door_edge >= 0 and plan.door_room >= 0:
            door_sector_by_endpoint[(plan.door_edge, plan.door_room)] = sector_idx
        for idx in range(len(polygon)):
            p1 = polygon[idx]
            p2 = polygon[(idx + 1) % len(polygon)]
            v1 = vertex_index(p1)
            v2 = vertex_index(p2)
            if v1 == v2:
                continue
            key = (v1, v2) if v1 < v2 else (v2, v1)
            edge_occurrences.setdefault(key, []).append((sector_idx, v1, v2, plan.wall_texture))

    for key in sorted(edge_occurrences.keys()):
        uses = edge_occurrences[key]
        if len(uses) == 1:
            sector_idx, v1, v2, wall_tex = uses[0]
            line_idx = add_boundary_line(
                map_data,
                v1_idx=v1,
                v2_idx=v2,
                right_sector=sector_idx,
                left_sector=-1,
                right_wall_texture=wall_tex,
                left_wall_texture=None,
            )
            if line_idx >= 0 and sector_kind.get(sector_idx, "") in door_gap_kinds:
                # Inside/back walls of door-gap side sectors should be floor-aligned.
                line = map_data.linedefs[line_idx]
                line.flags &= ~0x0008
                line.flags |= 0x0010
                if line.right >= 0:
                    map_data.sidedefs[line.right].offset_y = 0
            continue

        if len(uses) == 2:
            a = uses[0]
            b = uses[1]
            if not (a[1] == b[2] and a[2] == b[1]):
                if b[1] == a[2] and b[2] == a[1]:
                    a, b = b, a
            right_tex = a[3]
            left_tex = b[3]
            a_kind = sector_kind.get(a[0], "")
            b_kind = sector_kind.get(b[0], "")
            v1 = map_data.vertices[a[1]]
            v2 = map_data.vertices[a[2]]
            line_len_sq = ((v2.x - v1.x) * (v2.x - v1.x)) + ((v2.y - v1.y) * (v2.y - v1.y))
            is_door_face = line_len_sq >= door_face_min_len_sq
            is_nonface_door_boundary = False
            if (a_kind == "door" and b_kind != "door") or (b_kind == "door" and a_kind != "door"):
                if is_door_face:
                    right_tex = door_texture
                    left_tex = door_texture
                else:
                    # Keep initial assignment neutral; exact DOORTRAK placement is
                    # applied explicitly on jamb lines after linedef creation.
                    frame_tex = b[3] if a_kind == "door" else a[3]
                    right_tex = frame_tex
                    left_tex = frame_tex
                    is_nonface_door_boundary = True
            a_is_door_gap = a_kind in door_gap_kinds
            b_is_door_gap = b_kind in door_gap_kinds
            lintel_boundary = (
                ((a_kind in lintel_kinds) ^ (b_kind in lintel_kinds))
                and a_kind != "door"
                and b_kind != "door"
            )
            door_gap_extension_boundary = (
                (a_is_door_gap and b_kind == "transition") or (b_is_door_gap and a_kind == "transition")
            )
            line_idx = add_boundary_line(
                map_data,
                v1_idx=a[1],
                v2_idx=a[2],
                right_sector=a[0],
                left_sector=b[0],
                right_wall_texture=right_tex,
                left_wall_texture=left_tex,
            )
            if line_idx >= 0:
                line = map_data.linedefs[line_idx]
                if lintel_boundary or door_gap_extension_boundary:
                    # Keep upper textures top-pegged so they stay aligned with the tops
                    # of neighboring room/corridor wall textures. This also applies
                    # to door-gap side sectors that extend the lintel left/right.
                    line.flags |= 0x0008
                    line.flags &= ~0x0010
                    if line.right >= 0:
                        rs = map_data.sidedefs[line.right]
                        rs.offset_y = 0
                    if line.left >= 0:
                        ls = map_data.sidedefs[line.left]
                        ls.offset_y = 0
                if is_nonface_door_boundary:
                    # Keep side gaps beside the slab as wall framing (not door slab texture).
                    if line.right >= 0:
                        rs = map_data.sidedefs[line.right]
                        wall_tex = right_tex if right_tex != door_texture else (left_tex if left_tex != door_texture else "STARTAN3")
                        rs.texture_top = wall_tex
                        rs.texture_middle = "-"
                        rs.texture_bottom = wall_tex
                    if line.left >= 0:
                        ls = map_data.sidedefs[line.left]
                        wall_tex = left_tex if left_tex != door_texture else (right_tex if right_tex != door_texture else "STARTAN3")
                        ls.texture_top = wall_tex
                        ls.texture_middle = "-"
                        ls.texture_bottom = wall_tex
                if a_kind == "door" and b_kind != "door":
                    door_lines_by_sector.setdefault(a[0], set()).add(line_idx)
                elif b_kind == "door" and a_kind != "door":
                    door_lines_by_sector.setdefault(b[0], set()).add(line_idx)
            continue

        # Non-manifold fallback: keep edges closed as one-sided walls.
        for sector_idx, v1, v2, wall_tex in uses:
            add_boundary_line(
                map_data,
                v1_idx=v1,
                v2_idx=v2,
                right_sector=sector_idx,
                left_sector=-1,
                right_wall_texture=wall_tex,
                left_wall_texture=None,
            )

    return map_data, door_lines_by_sector, door_sector_by_endpoint, room_sector_by_room_index


def local_polygon_from_grid_cells(
    cells: set[tuple[int, int]],
    cell_size: float = PLATFORM_EDGE_UNITS,
) -> list[tuple[float, float]]:
    if not cells:
        return []

    edges: set[tuple[tuple[float, float], tuple[float, float]]] = set()
    for ix, iy in cells:
        left = float(ix) - 0.5
        right = float(ix) + 0.5
        bottom = float(iy) - 0.5
        top = float(iy) + 0.5
        if (ix, iy - 1) not in cells:
            edges.add(((left, bottom), (right, bottom)))
        if (ix + 1, iy) not in cells:
            edges.add(((right, bottom), (right, top)))
        if (ix, iy + 1) not in cells:
            edges.add(((right, top), (left, top)))
        if (ix - 1, iy) not in cells:
            edges.add(((left, top), (left, bottom)))

    if not edges:
        return []

    next_by_start: dict[tuple[float, float], list[tuple[float, float]]] = {}
    for start, end in edges:
        next_by_start.setdefault(start, []).append(end)

    visited_edges: set[tuple[tuple[float, float], tuple[float, float]]] = set()
    loops: list[list[tuple[float, float]]] = []
    for edge in sorted(edges):
        if edge in visited_edges:
            continue
        start, end = edge
        loop = [start, end]
        visited_edges.add(edge)
        current = end
        while current != start:
            candidates = [cand for cand in next_by_start.get(current, []) if (current, cand) not in visited_edges]
            if not candidates:
                break
            nxt = sorted(candidates)[0]
            visited_edges.add((current, nxt))
            current = nxt
            loop.append(current)
        if len(loop) >= 4 and loop[0] == loop[-1]:
            loops.append(loop[:-1])

    if not loops:
        return []

    def loop_area(loop_points: list[tuple[float, float]]) -> float:
        return abs(signed_area(tuple(loop_points)))

    outer = max(loops, key=loop_area)
    poly = [(px * float(cell_size), py * float(cell_size)) for px, py in outer]
    return normalize_detail_polygon(poly)


def collapse_short_edges(
    points: list[tuple[float, float]],
    min_spacing: float,
) -> list[tuple[float, float]]:
    if len(points) < 3:
        return points
    min_spacing_sq = float(min_spacing) * float(min_spacing)
    reduced: list[tuple[float, float]] = []
    for px, py in points:
        if not reduced:
            reduced.append((px, py))
            continue
        dx = px - reduced[-1][0]
        dy = py - reduced[-1][1]
        if (dx * dx) + (dy * dy) >= min_spacing_sq:
            reduced.append((px, py))
    if len(reduced) > 1:
        dx0 = reduced[0][0] - reduced[-1][0]
        dy0 = reduced[0][1] - reduced[-1][1]
        if (dx0 * dx0) + (dy0 * dy0) < min_spacing_sq:
            reduced.pop()
    return reduced if len(reduced) >= 3 else points


def postprocess_puddle_local_polygon(
    base_poly: list[tuple[float, float]],
    rng: random.Random,
    cell_size: float = PLATFORM_EDGE_UNITS,
) -> list[tuple[float, float]]:
    base = normalize_detail_polygon(list(base_poly))
    if len(base) < 3:
        return base
    force_base_output = bool(DEBUG_DISABLE_PUDDLE_JAGGED)
    base_area = polygon_area_abs(tuple(base))
    if base_area < 512.0:
        return base

    centroid_x = sum(x for x, _ in base) / float(len(base))
    centroid_y = sum(y for _, y in base) / float(len(base))
    min_spacing = max(PUDDLE_MIN_VERTEX_SPACING_UNITS, float(cell_size) * 0.10)
    max_amp = float(cell_size) * PUDDLE_WAVE_AMPLITUDE_FACTOR
    base_amp = min(max_amp, max(6.0, math.sqrt(base_area) * 0.18))

    amp_scales = tuple(scale / 100.0 for scale in range(100, 0, -5))
    for amp_scale in amp_scales:
        working = list(base)
        amp = base_amp * amp_scale

        for _ in range(PUDDLE_POSTPROCESS_PASSES):
            warped: list[tuple[float, float]] = []
            count = len(working)
            for idx in range(count):
                p0 = working[idx]
                p1 = working[(idx + 1) % count]
                q = v_lerp(p0, p1, PUDDLE_CORNER_CUT_RATIO)
                r = v_lerp(p0, p1, 1.0 - PUDDLE_CORNER_CUT_RATIO)
                edge = v_sub(p1, p0)
                edge_len = v_len(edge)
                if edge_len > 1.0e-6:
                    tangent = (edge[0] / edge_len, edge[1] / edge_len)
                    normal = v_perp(tangent)
                    midpoint = v_mid(p0, p1)
                    # Robust outward normal selection: centroid heuristics break on
                    # concave/L-shape edges, causing self-intersections and fallback.
                    probe_eps = max(2.0, min(amp * 0.25, float(cell_size) * 0.20))
                    probe_point = (midpoint[0] + (normal[0] * probe_eps), midpoint[1] + (normal[1] * probe_eps))
                    if point_in_polygon(probe_point, tuple(working)):
                        normal = (-normal[0], -normal[1])
                    wave = rng.uniform(-1.0, 1.0)
                    bulge = amp * (0.20 + (0.80 * abs(wave)))
                    if wave < 0.0:
                        bulge *= -0.45
                    q = (q[0] + (normal[0] * bulge * 0.45), q[1] + (normal[1] * bulge * 0.45))
                    r = (r[0] + (normal[0] * bulge * 0.80), r[1] + (normal[1] * bulge * 0.80))
                warped.append(q)
                warped.append(r)
            working = normalize_detail_polygon(collapse_short_edges(warped, min_spacing))
            if len(working) < 3:
                break

        if len(working) < 3:
            continue

        rippled: list[tuple[float, float]] = []
        for px, py in working:
            vx = px - centroid_x
            vy = py - centroid_y
            distance = math.hypot(vx, vy)
            if distance <= 1.0e-6:
                rippled.append((px, py))
                continue
            radial_scale = 1.0 + rng.uniform(-0.04, 0.08)
            tangent = (-vy / distance, vx / distance)
            tangent_shift = rng.uniform(-0.06, 0.06) * amp
            rippled.append(
                (
                    centroid_x + (vx * radial_scale) + (tangent[0] * tangent_shift),
                    centroid_y + (vy * radial_scale) + (tangent[1] * tangent_shift),
                )
            )

        candidate = normalize_detail_polygon(collapse_short_edges(rippled, min_spacing))
        if len(candidate) < 3:
            continue
        if polygon_self_intersects(tuple(candidate)):
            continue
        candidate_area = polygon_area_abs(tuple(candidate))
        if candidate_area < (base_area * PUDDLE_MIN_AREA_SCALE):
            continue
        if candidate_area > (base_area * PUDDLE_MAX_AREA_SCALE):
            continue
        if force_base_output:
            # Debug mode: keep pool shape simple while preserving RNG flow.
            return base
        return candidate

    # Last resort for concave pools: add stable chamfers so we still avoid
    # perfectly blocky orthogonal outlines when noise candidates are rejected.
    if not force_base_output and len(base) >= 4:
        chamfered: list[tuple[float, float]] = []
        for idx in range(len(base)):
            p0 = base[idx]
            p1 = base[(idx + 1) % len(base)]
            chamfered.append(v_lerp(p0, p1, 0.28))
            chamfered.append(v_lerp(p0, p1, 0.72))
        chamfered = normalize_detail_polygon(collapse_short_edges(chamfered, min_spacing))
        if (
            len(chamfered) >= 3
            and not polygon_self_intersects(tuple(chamfered))
        ):
            chamfer_area = polygon_area_abs(tuple(chamfered))
            if (base_area * PUDDLE_MIN_AREA_SCALE) <= chamfer_area <= (base_area * PUDDLE_MAX_AREA_SCALE):
                return chamfered

    return base


def add_room_internal_sectors(
    map_data: MutableMap,
    layout: PolyLayout,
    room_sector_lookup: dict[int, int],
    theme: ThemeStyle,
    theme_name: str,
    rng: random.Random,
    room_idx: int,
    pool_state: dict[str, int] | None = None,
) -> tuple[
    int,
    dict[int, list[tuple[tuple[float, float], ...]]],
    dict[int, list[tuple[tuple[float, float], ...]]],
    list[tuple[tuple[tuple[float, float], ...], int]],
    dict[int, list[tuple[tuple[float, float], ...]]],
    dict[int, list[tuple[float, float]]],
]:
    # *** PASS 1: Decide internal-sector plan for this room (count + kinds) ***
    # *** PASS 2: Build room-local placement grid and reserve blocked/buffer cells ***
    # *** PASS 3: Place internal sectors with retry loop and geometry validation ***
    # *** PASS 4: Apply fallback single-cell placement where main placement fails ***
    # *** PASS 5: Store outputs for this room (blocked/sunken masks, decor jobs, free-point pool) ***
    vertex_lookup: dict[tuple[int, int], int] = {
        (vertex.x, vertex.y): idx for idx, vertex in enumerate(map_data.vertices)
    }
    placed_total = 0
    blocked_local_polys_by_room: dict[int, list[tuple[tuple[float, float], ...]]] = {}
    sunken_local_polys_by_room: dict[int, list[tuple[tuple[float, float], ...]]] = {}
    all_platform_local_polys_by_room: dict[int, list[tuple[tuple[float, float], ...]]] = {}
    all_platform_world_polys: list[tuple[tuple[float, float], ...]] = []
    free_mask_local_points_by_room: dict[int, list[tuple[float, float]]] = {}
    decor_jobs: list[tuple[tuple[tuple[float, float], ...], int]] = []
    liquid_flat = theme.liquid_floor
    platform_decor_pool = SMALL_PLATFORM_DECOR_BY_THEME.get(theme_name, SMALL_PLATFORM_DECOR_BY_THEME["urban"])
    if pool_state is None:
        pool_state = {}
    placed_puddle_count = int(pool_state.get("placed_puddle_count", 0))

    def vertex_index_world(point: tuple[float, float]) -> int:
        key = (int(round(point[0])), int(round(point[1])))
        if key in vertex_lookup:
            return vertex_lookup[key]
        map_data.vertices.append(Vertex(key[0], key[1]))
        idx = len(map_data.vertices) - 1
        vertex_lookup[key] = idx
        return idx

    target_room_idx = room_idx
    if target_room_idx < 0 or target_room_idx >= len(layout.rooms):
        return (
            placed_total,
            blocked_local_polys_by_room,
            sunken_local_polys_by_room,
            decor_jobs,
            all_platform_local_polys_by_room,
            free_mask_local_points_by_room,
        )
    room_idx = target_room_idx
    room = layout.rooms[room_idx]
    room_sector = room_sector_lookup.get(room_idx)
    map_name = map_data.name.strip().upper()
    debug_blue_room = diagnostic_focus_room_index(map_data, layout)
    verbose_blue_room = verbose_geom_debug_enabled(map_name) and room_idx == debug_blue_room
    if verbose_blue_room:
        log_diag(
            f"[MAPDBG] map={map_name} INTERNAL_BEGIN room={room_idx} room_sector={room_sector} "
            f"room_center=({room.center[0]:.2f},{room.center[1]:.2f}) poly_verts={len(room.polygon)}"
        )
        for idx, pt in enumerate(room.polygon):
            log_diag(
                f"[MAPDBG] map={map_name} INTERNAL_ROOM_POLY room={room_idx} idx={idx} "
                f"x={pt[0]:.3f} y={pt[1]:.3f}"
            )
    if room_sector is None:
        return (
            placed_total,
            blocked_local_polys_by_room,
            sunken_local_polys_by_room,
            decor_jobs,
            all_platform_local_polys_by_room,
            free_mask_local_points_by_room,
        )
    else:
        room_boundary_world = tuple(room_polygon_with_door_splits(room, {}))
        room_boundary_world_i = normalize_plan_polygon(tuple(room_boundary_world))
        room_boundary_world_snapped = tuple((float(x), float(y)) for x, y in room_boundary_world_i)
        wall_clearance_sq = INTERNAL_SECTOR_WALL_CLEARANCE_UNITS * INTERNAL_SECTOR_WALL_CLEARANCE_UNITS
        room_boundary_segments_world: list[tuple[tuple[float, float], tuple[float, float]]] = []
        for line in map_data.linedefs:
            right_sector = (
                map_data.sidedefs[line.right].sector
                if 0 <= line.right < len(map_data.sidedefs)
                else -1
            )
            left_sector = (
                map_data.sidedefs[line.left].sector
                if 0 <= line.left < len(map_data.sidedefs)
                else -1
            )
            if right_sector != room_sector and left_sector != room_sector:
                continue
            if right_sector == room_sector and left_sector == room_sector:
                continue
            if not (0 <= line.v1 < len(map_data.vertices) and 0 <= line.v2 < len(map_data.vertices)):
                continue
            v1 = map_data.vertices[line.v1]
            v2 = map_data.vertices[line.v2]
            if v1.x == v2.x and v1.y == v2.y:
                continue
            room_boundary_segments_world.append(
                ((float(v1.x), float(v1.y)), (float(v2.x), float(v2.y)))
            )
        room_floor = map_data.sectors[room_sector].floor_height
        room_ceiling = map_data.sectors[room_sector].ceiling_height
        room_light = map_data.sectors[room_sector].light_level
    
        # *** PASS 1: Decide internal-sector plan for this room (count + kinds) ***
        puddle_prob = max(0.0, min(0.95, float(PUDDLE_SECTOR_PROBABILITY)))
        non_puddle_base = (
            ("high_box_sector", 0.40),
            ("medium_box_sector", 0.40),
            ("low_box_sector", 0.05),
            ("walkable_sector", 0.05),
        )
        non_puddle_total = sum(weight for _name, weight in non_puddle_base)
        non_puddle_scale = (1.0 - puddle_prob) / max(1.0e-6, non_puddle_total)
        mode_weighted_kinds = (
            ("high_box_sector", non_puddle_base[0][1] * non_puddle_scale),
            ("medium_box_sector", non_puddle_base[1][1] * non_puddle_scale),
            ("puddle_sector", puddle_prob),
            ("low_box_sector", non_puddle_base[2][1] * non_puddle_scale),
            ("walkable_sector", non_puddle_base[3][1] * non_puddle_scale),
        )

        def choose_weighted_platform_kind() -> str:
            roll = rng.random()
            cumulative = 0.0
            for kind_name, chance in mode_weighted_kinds:
                cumulative += chance
                if roll < cumulative:
                    return kind_name
            return mode_weighted_kinds[-1][0]

        room_platform_mode = rng.randrange(4)
        if room_platform_mode == 0:
            platform_plan = ["puddle_sector"] # Lake room
        elif room_platform_mode == 1:
            platform_plan = [choose_weighted_platform_kind() for _ in range(2)] # Random few
        elif room_platform_mode == 2:
            platform_plan = [choose_weighted_platform_kind() for _ in range(3)] # Random many
        else:
            platform_plan = [choose_weighted_platform_kind() for _ in range(4)] # Storage room
        log_trace(
            f"SECTOR_ROOM_PLAN room={room_idx} mode={room_platform_mode} "
            f"plan={','.join(platform_plan)}"
        )

        door_sides = set(layout.room_door_sides[room_idx]) if room_idx < len(layout.room_door_sides) else set()
        half_len = room.half_length
        half_wid = room.half_width
        room_full_len = half_len * 2.0
        room_full_wid = half_wid * 2.0
        max_sector_span_x = room_full_len * INTERNAL_SECTOR_MAX_DIM_FRACTION
        max_sector_span_y = room_full_wid * INTERNAL_SECTOR_MAX_DIM_FRACTION
        room_area = max(1.0, polygon_area_abs(room.polygon))
        max_room_sector_area = room_area * INTERNAL_SECTOR_MAX_ROOM_COVERAGE
        placed_room_sector_area = 0.0
        edge_margin = MIN_WALKABLE_GAP_WIDTH
        cell_size = float(PLATFORM_EDGE_UNITS)
        half_cell = cell_size * 0.5
        free_state = CellOccupancy.FREE
        buffer_state = CellOccupancy.BUFFER
        occupied_state = CellOccupancy.OCCUPIED
        cell_state: dict[CellXY, CellOccupancy] = {}
        # Keep only a narrow approach clear near doorway centers.
        door_depth_clear = 180.0
        door_lane_half = 116.0
        quadrants = [(-1.0, -1.0), (-1.0, 1.0), (1.0, -1.0), (1.0, 1.0)]

        cx_min = int(math.floor(((-half_len) / cell_size))) - 1
        cx_max = int(math.ceil(((half_len) / cell_size))) + 1
        cy_min = int(math.floor(((-half_wid) / cell_size))) - 1
        cy_max = int(math.ceil(((half_wid) / cell_size))) + 1
        for iy in range(cy_min, cy_max + 1):
            for ix in range(cx_min, cx_max + 1):
                cell_state[CellXY(ix, iy)] = free_state

        wall_buffer_sq = (INTERNAL_SECTOR_WALL_CLEARANCE_UNITS + half_cell) * (INTERNAL_SECTOR_WALL_CLEARANCE_UNITS + half_cell)
        def local_polys_overlap(
            poly_a: tuple[tuple[float, float], ...],
            poly_b: tuple[tuple[float, float], ...],
        ) -> bool:
            if min_edge_distance_between_polygons_sq(poly_a, poly_b) <= 1.0e-6:
                return True
            if any(point_in_polygon(point, poly_b) for point in poly_a):
                return True
            if any(point_in_polygon(point, poly_a) for point in poly_b):
                return True
            return False

        # *** PASS 2: Build room-local placement grid and reserve blocked/buffer cells ***
        for iy in range(cy_min, cy_max + 1):
            ly = float(iy) * cell_size
            for ix in range(cx_min, cx_max + 1):
                lx = float(ix) * cell_size
                cell = CellXY(ix, iy)
                if cell_state.get(cell) != free_state:
                    continue
                if not point_in_room_local_shape(room, lx, ly):
                    cell_state[cell] = buffer_state
                    continue
                # Keep doorway approach regions clear for grid seeds/growth too.
                if "front" in door_sides and lx > (half_len - door_depth_clear) and abs(ly) < door_lane_half:
                    cell_state[cell] = buffer_state
                    continue
                if "back" in door_sides and lx < (-half_len + door_depth_clear) and abs(ly) < door_lane_half:
                    cell_state[cell] = buffer_state
                    continue
                if "left" in door_sides and ly > (half_wid - door_depth_clear) and abs(lx) < door_lane_half:
                    cell_state[cell] = buffer_state
                    continue
                if "right" in door_sides and ly < (-half_wid + door_depth_clear) and abs(lx) < door_lane_half:
                    cell_state[cell] = buffer_state
                    continue
                wx, wy = local_to_world(room.center, room.tangent, room.normal, lx, ly)
                point_world = (float(wx), float(wy))
                if any(
                    point_to_segment_distance_sq(point_world, a, b) < wall_buffer_sq
                    for a, b in room_boundary_segments_world
                ):
                    cell_state[cell] = buffer_state

        # *** PASS 3: Place internal sectors with retry loop and geometry validation ***
        for platform_kind in platform_plan:
            is_killing_pool_slot = (
                platform_kind == "puddle_sector"
                and rng.random() < KILLING_POOL_PROBABILITY
            )
            if placed_room_sector_area >= (max_room_sector_area - (cell_size * cell_size)):
                log_trace(
                    f"SECTOR_SKIP_AREA_BUDGET room={room_idx} kind={platform_kind} "
                    f"used={placed_room_sector_area:.1f} max={max_room_sector_area:.1f}"
                )
                continue
            if not any(state == free_state for state in cell_state.values()):
                log_trace(f"SECTOR_SKIP_NO_FREE room={room_idx} kind={platform_kind}")
                continue
            placed_this_slot = False

            for attempt_idx in range(1, MAX_RETRIES + 1):
                log_trace(
                    f"SECTOR_ATTEMPT room={room_idx} kind={platform_kind} attempt={attempt_idx}/{MAX_RETRIES}"
                )
                compact = attempt_idx > (MAX_RETRIES // 2)
                is_l_shape = (rng.random() < 0.40) or (platform_kind == "puddle_sector")
                t = (attempt_idx - 1) / float(max(1, MAX_RETRIES - 1))
                sunken_boost = 5.0 - (4.0 * t) if platform_kind == "puddle_sector" else 1.0

                base_w_cells = rng.choice((1, 2, 3, 4, 5, 6 if not compact else 4))
                base_h_cells = rng.choice((1, 2, 3, 4, 5, 6 if not compact else 4))
                target_w_cells = max(1, int(round(float(base_w_cells) * float(sunken_boost))))
                target_h_cells = max(1, int(round(float(base_h_cells) * float(sunken_boost))))
                max_w_cells = max(1, int(math.floor(max_sector_span_x / cell_size)))
                max_h_cells = max(1, int(math.floor(max_sector_span_y / cell_size)))
                target_w_cells = min(target_w_cells, max_w_cells)
                target_h_cells = min(target_h_cells, max_h_cells)
                remaining_area = max(0.0, max_room_sector_area - placed_room_sector_area)
                max_cells_by_area = max(1, int(math.floor(remaining_area / (cell_size * cell_size))))
                while (target_w_cells * target_h_cells) > max_cells_by_area and (target_w_cells > 1 or target_h_cells > 1):
                    if target_w_cells >= target_h_cells and target_w_cells > 1:
                        target_w_cells -= 1
                    elif target_h_cells > 1:
                        target_h_cells -= 1

                free_cells = [cell for cell, state in cell_state.items() if state == free_state]
                if not free_cells:
                    break
                qx, qy = rng.choice(quadrants)
                quadrant_cells = [
                    (ix, iy)
                    for ix, iy in free_cells
                    if (ix >= 0) == (qx > 0) and (iy >= 0) == (qy > 0)
                ]
                seed = rng.choice(quadrant_cells if quadrant_cells else free_cells)
                claimed_cells: set[CellXY] = {seed}
                x_left = x_right = seed[0]
                y_bottom = y_top = seed[1]

                def cell_is_claimable(cell: CellXY) -> bool:
                    if cell in claimed_cells:
                        return True
                    return cell_state.get(cell, buffer_state) == free_state

                # Grow width first: +X until blocked, then -X until blocked (or desired width reached).
                while ((x_right - x_left) + 1) < target_w_cells:
                    nx = x_right + 1
                    candidate_cells = [CellXY(nx, y) for y in range(y_bottom, y_top + 1)]
                    if all(cell_is_claimable(cell) for cell in candidate_cells):
                        claimed_cells.update(candidate_cells)
                        x_right = nx
                    else:
                        break
                while ((x_right - x_left) + 1) < target_w_cells:
                    nx = x_left - 1
                    candidate_cells = [CellXY(nx, y) for y in range(y_bottom, y_top + 1)]
                    if all(cell_is_claimable(cell) for cell in candidate_cells):
                        claimed_cells.update(candidate_cells)
                        x_left = nx
                    else:
                        break

                # Then grow height in one chosen direction (+Y or -Y).
                y_direction = 1 if rng.random() < 0.5 else -1
                while ((y_top - y_bottom) + 1) < target_h_cells:
                    ny = y_top + 1 if y_direction > 0 else y_bottom - 1
                    candidate_cells = [CellXY(x, ny) for x in range(x_left, x_right + 1)]
                    if all(cell_is_claimable(cell) for cell in candidate_cells):
                        claimed_cells.update(candidate_cells)
                        if y_direction > 0:
                            y_top = ny
                        else:
                            y_bottom = ny
                    else:
                        break

                if is_l_shape and rng.random() < 0.65:
                    corner = rng.choice(("ne", "nw", "se", "sw"))
                    if corner == "ne":
                        side = rng.choice(("+x", "+y"))
                    elif corner == "nw":
                        side = rng.choice(("-x", "+y"))
                    elif corner == "se":
                        side = rng.choice(("+x", "-y"))
                    else:
                        side = rng.choice(("-x", "-y"))
                    arm_steps = rng.randint(1, max(1, int(round((target_w_cells + target_h_cells) * 0.25))))
                    if side in {"+x", "-x"}:
                        max_thickness = max(1, ((y_top - y_bottom) + 1) // 2)
                        thickness = rng.randint(1, max_thickness)
                        if corner in {"ne", "nw"}:
                            end_y = y_top
                            start_y = max(y_bottom, y_top - thickness + 1)
                        else:
                            start_y = y_bottom
                            end_y = min(y_top, y_bottom + thickness - 1)
                        for _ in range(arm_steps):
                            nx = x_right + 1 if side == "+x" else x_left - 1
                            candidate_cells = [CellXY(nx, y) for y in range(start_y, end_y + 1)]
                            if not all(cell_is_claimable(cell) for cell in candidate_cells):
                                break
                            claimed_cells.update(candidate_cells)
                            if side == "+x":
                                x_right = nx
                            else:
                                x_left = nx
                    else:
                        max_thickness = max(1, ((x_right - x_left) + 1) // 2)
                        thickness = rng.randint(1, max_thickness)
                        if corner in {"ne", "se"}:
                            end_x = x_right
                            start_x = max(x_left, x_right - thickness + 1)
                        else:
                            start_x = x_left
                            end_x = min(x_right, x_left + thickness - 1)
                        for _ in range(arm_steps):
                            ny = y_top + 1 if side == "+y" else y_bottom - 1
                            candidate_cells = [CellXY(x, ny) for x in range(start_x, end_x + 1)]
                            if not all(cell_is_claimable(cell) for cell in candidate_cells):
                                break
                            claimed_cells.update(candidate_cells)
                            if side == "+y":
                                y_top = ny
                            else:
                                y_bottom = ny

                local_poly = local_polygon_from_grid_cells(claimed_cells, cell_size=cell_size)
                if platform_kind == "puddle_sector":
                    local_poly = postprocess_puddle_local_polygon(local_poly, rng, cell_size=cell_size)
                if len(local_poly) < 3:
                    continue
                if polygon_self_intersects(tuple(local_poly)):
                    continue
                if not polygon_inside_room_local_shape(room, local_poly):
                    continue

                cx = float(seed[0]) * cell_size
                cy = float(seed[1]) * cell_size
                log_trace(
                    f"SECTOR_ATTEMPT_LOCAL room={room_idx} kind={platform_kind} attempt={attempt_idx}/{MAX_RETRIES} "
                    f"center_local=({cx:.1f},{cy:.1f}) cells={len(claimed_cells)} l_shape={is_l_shape}"
                )

                bbox = local_poly_bbox(local_poly)
                minx, maxx, miny, maxy = bbox
                span_x = maxx - minx
                span_y = maxy - miny
                if span_x > max_sector_span_x or span_y > max_sector_span_y:
                    continue
                candidate_area = polygon_area_abs(tuple(local_poly))
                if (placed_room_sector_area + candidate_area) > max_room_sector_area:
                    continue
                log_trace(
                    f"SECTOR_ATTEMPT_LOCAL_BBOX room={room_idx} kind={platform_kind} attempt={attempt_idx}/{MAX_RETRIES} "
                    f"bbox_local=({minx:.1f},{miny:.1f})-({maxx:.1f},{maxy:.1f})"
                )

                # Keep doorway approach regions clear by side (centered lane only).
                if (
                    "front" in door_sides
                    and maxx > (half_len - door_depth_clear)
                    and miny < door_lane_half
                    and maxy > -door_lane_half
                ):
                    continue
                if (
                    "back" in door_sides
                    and minx < (-half_len + door_depth_clear)
                    and miny < door_lane_half
                    and maxy > -door_lane_half
                ):
                    continue
                if (
                    "left" in door_sides
                    and maxy > (half_wid - door_depth_clear)
                    and minx < door_lane_half
                    and maxx > -door_lane_half
                ):
                    continue
                if (
                    "right" in door_sides
                    and miny < (-half_wid + door_depth_clear)
                    and minx < door_lane_half
                    and maxx > -door_lane_half
                ):
                    continue

                if minx < (-half_len + edge_margin) or maxx > (half_len - edge_margin):
                    continue
                if miny < (-half_wid + edge_margin) or maxy > (half_wid - edge_margin):
                    continue
                candidate_local_poly = tuple(local_poly)
                if any(
                    local_polys_overlap(candidate_local_poly, prior_poly)
                    for prior_poly in all_platform_local_polys_by_room.get(room_idx, [])
                ):
                    continue

                floor_tex = theme.transition_floor if rng.random() < 0.45 else theme.room_floor
                floor_h = room_floor + 24
                ceil_h = room_ceiling
                light = room_light
                sector_special = 0
                blocks_walk = False

                if platform_kind in {"high_box_sector", "medium_box_sector"}:
                    use_gray_box_variant = rng.random() < PLATFORM_GRAY_VARIANT_CHANCE
                else:
                    use_gray_box_variant = False

                if platform_kind == "high_box_sector":
                    # Original ceiling-blocker style: a near-ceiling raised floor sector.
                    floor_h = min(room_ceiling, room_floor + 128)
                    floor_tex = PLATFORM_CRATE_TOP_FLAT_GRAY if use_gray_box_variant else PLATFORM_CRATE_TOP_FLAT
                    blocks_walk = True
                elif platform_kind == "medium_box_sector":
                    floor_h = min(room_ceiling, room_floor + 64)
                    floor_tex = PLATFORM_CRATE_TOP_FLAT_GRAY if use_gray_box_variant else PLATFORM_CRATE_TOP_FLAT
                    blocks_walk = True
                elif platform_kind == "low_box_sector":
                    floor_h = min(room_ceiling, room_floor + 32)
                    floor_tex = PLATFORM_BLOCKING_TOP_FLAT
                    blocks_walk = True
                elif platform_kind == "walkable_sector":
                    # Max normal step-up height in Doom.
                    floor_h = room_floor + 24
                else:
                    # Every Nth pool becomes a killing pool that is just
                    # deep enough to prevent stepping back out.
                    pool_depth_units = KILLING_POOL_DEPTH_UNITS if is_killing_pool_slot else ROOM_SUNKEN_PLATFORM_DEPTH_UNITS
                    floor_h = room_floor - pool_depth_units
                    floor_tex = KILLING_POOL_FLOOR_TEXTURE if is_killing_pool_slot else liquid_flat
                    light = room_light
                    sector_special = SUNKEN_POOL_DAMAGE_SPECIAL
                # Re-check bbox and area after sector-floor selection.
                bbox = local_poly_bbox(local_poly)
                minx, maxx, miny, maxy = bbox
                span_x = maxx - minx
                span_y = maxy - miny
                if span_x > max_sector_span_x or span_y > max_sector_span_y:
                    continue
                candidate_area = polygon_area_abs(tuple(local_poly))
                if (placed_room_sector_area + candidate_area) > max_room_sector_area:
                    continue
                candidate_local_poly = tuple(local_poly)
                if any(
                    local_polys_overlap(candidate_local_poly, prior_poly)
                    for prior_poly in all_platform_local_polys_by_room.get(room_idx, [])
                ):
                    continue

                world_poly = [
                    local_to_world(room.center, room.tangent, room.normal, lx, ly)
                    for lx, ly in local_poly
                ]
                world_poly = normalize_detail_polygon(world_poly)
                if len(world_poly) < 3:
                    continue
                snapped_world_poly_i = normalize_plan_polygon(tuple(world_poly))
                if len(snapped_world_poly_i) < 3:
                    continue
                if abs(signed_area(snapped_world_poly_i)) < 2048.0:
                    continue
                snapped_world_poly = tuple((float(x), float(y)) for x, y in snapped_world_poly_i)
                if polygon_self_intersects(snapped_world_poly):
                    continue
                # Keep a guaranteed walkable lane between internal sectors and room walls.
                if (
                    min_edge_distance_between_polygons_sq(
                        snapped_world_poly,
                        room_boundary_world_snapped,
                    )
                    < wall_clearance_sq
                ):
                    continue
                if (
                    min_edge_distance_polygon_to_segments_sq(
                        snapped_world_poly,
                        room_boundary_segments_world,
                    )
                    < wall_clearance_sq
                ):
                    continue
                vertex_indices_raw = [
                    vertex_index_world((float(x), float(y)))
                    for x, y in snapped_world_poly_i
                ]
                vertex_indices: list[int] = []
                for vertex_idx in vertex_indices_raw:
                    if not vertex_indices or vertex_indices[-1] != vertex_idx:
                        vertex_indices.append(vertex_idx)
                if len(vertex_indices) > 1 and vertex_indices[0] == vertex_indices[-1]:
                    vertex_indices.pop()
                if len(vertex_indices) < 3:
                    continue
                if len(set(vertex_indices)) < 3:
                    continue
                final_world_poly = tuple(
                    (float(map_data.vertices[vertex_idx].x), float(map_data.vertices[vertex_idx].y))
                    for vertex_idx in vertex_indices
                )
                if verbose_blue_room:
                    log_diag(
                        f"[MAPDBG] map={map_name} INTERNAL_CANDIDATE room={room_idx} kind={platform_kind} "
                        f"attempt={attempt_idx}/{MAX_RETRIES} vertex_indices={vertex_indices}"
                    )
                    for p_idx, (wx, wy) in enumerate(final_world_poly):
                        log_diag(
                            f"[MAPDBG] map={map_name} INTERNAL_CANDIDATE_V room={room_idx} kind={platform_kind} "
                            f"attempt={attempt_idx}/{MAX_RETRIES} idx={p_idx} x={wx:.3f} y={wy:.3f}"
                        )
                final_world_poly_i = normalize_plan_polygon(
                    tuple((int(round(x)), int(round(y))) for x, y in final_world_poly)
                )
                final_world_poly_i = collapse_short_polygon_edges(
                    final_world_poly_i,
                    min_edge_units=float(INTERNAL_SECTOR_MIN_EDGE_UNITS),
                )
                if len(final_world_poly_i) < 3:
                    continue
                if abs(signed_area(final_world_poly_i)) < 2048.0:
                    continue
                vertex_indices_raw = [
                    vertex_index_world((float(x), float(y)))
                    for x, y in final_world_poly_i
                ]
                vertex_indices = []
                for vertex_idx in vertex_indices_raw:
                    if not vertex_indices or vertex_indices[-1] != vertex_idx:
                        vertex_indices.append(vertex_idx)
                if len(vertex_indices) > 1 and vertex_indices[0] == vertex_indices[-1]:
                    vertex_indices.pop()
                if len(vertex_indices) < 3 or len(set(vertex_indices)) < 3:
                    continue
                final_world_poly_snapped = tuple((float(x), float(y)) for x, y in final_world_poly_i)
                if any(
                    local_polys_overlap(final_world_poly_snapped, prior_poly)
                    for prior_poly in all_platform_world_polys
                ):
                    continue
                fxs = [p[0] for p in final_world_poly_snapped]
                fys = [p[1] for p in final_world_poly_snapped]
                log_trace(
                    f"SECTOR_ATTEMPT_WORLD room={room_idx} kind={platform_kind} attempt={attempt_idx}/{MAX_RETRIES} "
                    f"bbox_world=({min(fxs):.1f},{min(fys):.1f})-({max(fxs):.1f},{max(fys):.1f})"
                )
                if polygon_self_intersects(final_world_poly_snapped):
                    continue
                min_boundary_dist_sq = min_edge_distance_between_polygons_sq(
                    final_world_poly_snapped,
                    room_boundary_world_snapped,
                )
                min_segment_dist_sq = min_edge_distance_polygon_to_segments_sq(
                    final_world_poly_snapped,
                    room_boundary_segments_world,
                )
                if min_boundary_dist_sq < wall_clearance_sq or min_segment_dist_sq < wall_clearance_sq:
                    if DEBUG_INTERNAL_SECTOR_PLACEMENT:
                        required = math.sqrt(wall_clearance_sq)
                        boundary_dist = math.sqrt(max(0.0, min_boundary_dist_sq))
                        segment_dist = math.sqrt(max(0.0, min_segment_dist_sq))
                        log_trace(
                            "SECTOR_REJECT_CLEARANCE "
                            f"(room={room_idx}, kind={platform_kind}, attempt={attempt_idx}/{MAX_RETRIES}, "
                            f"required={required:.1f}, boundary={boundary_dist:.1f}, segments={segment_dist:.1f})"
                        )
                    continue

                detail_sector = add_sector(
                    map_data,
                    floor_height=floor_h,
                    ceiling_height=ceil_h,
                    floor_texture=floor_tex,
                    ceiling_texture=theme.ceiling_flat,
                    light_level=light,
                    special=sector_special,
                )

                if platform_kind in {"high_box_sector", "medium_box_sector"}:
                    wall_tex = PLATFORM_CRATE_SIDE_TEXTURE_GRAY if use_gray_box_variant else PLATFORM_CRATE_SIDE_TEXTURE
                elif platform_kind == "low_box_sector":
                    wall_tex = PLATFORM_BLOCKING_SIDE_TEXTURE
                else:
                    wall_tex = theme.transition_wall_textures[0]
                detail_lines: list[int] = []
                for idx in range(len(vertex_indices)):
                    v1 = vertex_indices[idx]
                    v2 = vertex_indices[(idx + 1) % len(vertex_indices)]
                    line_idx = add_boundary_line(
                        map_data,
                        v1_idx=v1,
                        v2_idx=v2,
                        right_sector=detail_sector,
                        left_sector=room_sector,
                        right_wall_texture=wall_tex,
                        left_wall_texture=wall_tex,
                    )
                    detail_lines.append(line_idx)
                if verbose_blue_room:
                    log_diag(
                        f"[MAPDBG] map={map_name} INTERNAL_PLACE room={room_idx} kind={platform_kind} "
                        f"sector={detail_sector} floor={floor_h} ceil={ceil_h} special={sector_special} "
                        f"lines={detail_lines}"
                    )
                    for line_idx in detail_lines:
                        if line_idx < 0 or line_idx >= len(map_data.linedefs):
                            continue
                        dline = map_data.linedefs[line_idx]
                        if not (0 <= dline.v1 < len(map_data.vertices) and 0 <= dline.v2 < len(map_data.vertices)):
                            continue
                        dv1 = map_data.vertices[dline.v1]
                        dv2 = map_data.vertices[dline.v2]
                        log_diag(
                            f"[MAPDBG] map={map_name} INTERNAL_LINE room={room_idx} sector={detail_sector} "
                            f"line={line_idx} v1={dline.v1}({dv1.x},{dv1.y}) "
                            f"v2={dline.v2}({dv2.x},{dv2.y}) flags=0x{dline.flags:04x} "
                            f"right={dline.right} left={dline.left}"
                        )

                if platform_kind in {"medium_box_sector", "low_box_sector", "walkable_sector"} and platform_decor_pool:
                    poly_world = final_world_poly_snapped
                    xs = [point[0] for point in poly_world]
                    ys = [point[1] for point in poly_world]
                    min_wx = min(xs)
                    max_wx = max(xs)
                    min_wy = min(ys)
                    max_wy = max(ys)
                    if (max_wx - min_wx) >= 20.0 and (max_wy - min_wy) >= 20.0:
                        base_target = rng.randint(1, 2)
                        area_scale = max(0.75, min(4.0, polygon_area_abs(poly_world) / 16384.0))
                        decor_target = stochastic_scaled_count(base_target, area_scale, rng, minimum=1)
                        decor_target = min(10, decor_target)
                        decor_jobs.append((poly_world, decor_target))

                placed_this_slot = True
                placed_total += 1
                placed_room_sector_area += candidate_area
                for ix, iy in claimed_cells:
                    cell_state[CellXY(ix, iy)] = occupied_state
                for ix, iy in claimed_cells:
                    for ox in (-1, 0, 1):
                        for oy in (-1, 0, 1):
                            neighbor = CellXY(ix + ox, iy + oy)
                            if neighbor in claimed_cells:
                                continue
                            if cell_state.get(neighbor) == free_state:
                                cell_state[neighbor] = buffer_state
                log_trace(
                    f"SECTOR_PLACE room={room_idx} kind={platform_kind} attempt={attempt_idx}/{MAX_RETRIES} "
                    f"floor={floor_h} ceil={ceil_h} special={sector_special} verts={len(vertex_indices)}"
                )
                if platform_kind == "puddle_sector":
                    placed_puddle_count += 1
                all_platform_local_polys_by_room.setdefault(room_idx, []).append(tuple(local_poly))
                all_platform_world_polys.append(final_world_poly_snapped)
                if blocks_walk:
                    blocked_local_polys_by_room.setdefault(room_idx, []).append(tuple(local_poly))
                elif platform_kind == "puddle_sector":
                    sunken_local_polys_by_room.setdefault(room_idx, []).append(tuple(local_poly))
                break

            # *** PASS 4: Apply fallback single-cell placement where main placement fails ***
            if not placed_this_slot:
                fallback_free_cells = [cell for cell, state in cell_state.items() if state == free_state]
                if not fallback_free_cells:
                    log_trace(f"SECTOR_SKIP_NO_FREE room={room_idx} kind={platform_kind}")
                    continue
                if fallback_free_cells:
                    seed_ix, seed_iy = rng.choice(fallback_free_cells)
                    one_cell_local_poly = local_polygon_from_grid_cells({(seed_ix, seed_iy)}, cell_size=cell_size)
                    if platform_kind == "puddle_sector":
                        one_cell_local_poly = postprocess_puddle_local_polygon(
                            one_cell_local_poly,
                            rng,
                            cell_size=cell_size,
                        )
                    if len(one_cell_local_poly) >= 3 and polygon_inside_room_local_shape(room, one_cell_local_poly):
                        one_cell_area = polygon_area_abs(tuple(one_cell_local_poly))
                        if (placed_room_sector_area + one_cell_area) > max_room_sector_area:
                            log_trace(
                                f"SECTOR_SKIP_AREA_BUDGET room={room_idx} kind={platform_kind} "
                                f"used={placed_room_sector_area:.1f} max={max_room_sector_area:.1f}"
                            )
                            continue
                        floor_tex = theme.transition_floor if rng.random() < 0.45 else theme.room_floor
                        floor_h = room_floor + 24
                        ceil_h = room_ceiling
                        light = room_light
                        sector_special = 0
                        blocks_walk = False
                        if platform_kind in {"high_box_sector", "medium_box_sector"}:
                            use_gray_box_variant = rng.random() < PLATFORM_GRAY_VARIANT_CHANCE
                        else:
                            use_gray_box_variant = False
                        if platform_kind == "high_box_sector":
                            floor_h = min(room_ceiling, room_floor + 128)
                            floor_tex = PLATFORM_CRATE_TOP_FLAT_GRAY if use_gray_box_variant else PLATFORM_CRATE_TOP_FLAT
                            blocks_walk = True
                        elif platform_kind == "medium_box_sector":
                            floor_h = min(room_ceiling, room_floor + 64)
                            floor_tex = PLATFORM_CRATE_TOP_FLAT_GRAY if use_gray_box_variant else PLATFORM_CRATE_TOP_FLAT
                            blocks_walk = True
                        elif platform_kind == "low_box_sector":
                            floor_h = min(room_ceiling, room_floor + 32)
                            floor_tex = PLATFORM_BLOCKING_TOP_FLAT
                            blocks_walk = True
                        elif platform_kind == "walkable_sector":
                            floor_h = room_floor + 24
                        else:
                            pool_depth_units = KILLING_POOL_DEPTH_UNITS if is_killing_pool_slot else ROOM_SUNKEN_PLATFORM_DEPTH_UNITS
                            floor_h = room_floor - pool_depth_units
                            floor_tex = KILLING_POOL_FLOOR_TEXTURE if is_killing_pool_slot else liquid_flat
                            sector_special = SUNKEN_POOL_DAMAGE_SPECIAL

                        world_poly = [
                            local_to_world(room.center, room.tangent, room.normal, lx, ly)
                            for lx, ly in one_cell_local_poly
                        ]
                        world_poly = normalize_detail_polygon(world_poly)
                        if len(world_poly) >= 3:
                            snapped_world_poly_i = normalize_plan_polygon(tuple(world_poly))
                            snapped_world_poly_i = collapse_short_polygon_edges(
                                snapped_world_poly_i,
                                min_edge_units=float(INTERNAL_SECTOR_MIN_EDGE_UNITS),
                            )
                            if len(snapped_world_poly_i) >= 3 and abs(signed_area(snapped_world_poly_i)) >= 2048.0:
                                snapped_world_poly = tuple((float(x), float(y)) for x, y in snapped_world_poly_i)
                                if not polygon_self_intersects(snapped_world_poly):
                                    if (
                                        min_edge_distance_between_polygons_sq(snapped_world_poly, room_boundary_world_snapped) >= wall_clearance_sq
                                        and min_edge_distance_polygon_to_segments_sq(snapped_world_poly, room_boundary_segments_world) >= wall_clearance_sq
                                    ):
                                        if any(
                                            local_polys_overlap(snapped_world_poly, prior_poly)
                                            for prior_poly in all_platform_world_polys
                                        ):
                                            continue
                                        vertex_indices_raw = [
                                            vertex_index_world((float(x), float(y)))
                                            for x, y in snapped_world_poly_i
                                        ]
                                        vertex_indices: list[int] = []
                                        for vertex_idx in vertex_indices_raw:
                                            if not vertex_indices or vertex_indices[-1] != vertex_idx:
                                                vertex_indices.append(vertex_idx)
                                        if len(vertex_indices) > 1 and vertex_indices[0] == vertex_indices[-1]:
                                            vertex_indices.pop()
                                        if len(vertex_indices) >= 3 and len(set(vertex_indices)) >= 3:
                                            detail_sector = add_sector(
                                                map_data,
                                                floor_height=floor_h,
                                                ceiling_height=ceil_h,
                                                floor_texture=floor_tex,
                                                ceiling_texture=theme.ceiling_flat,
                                                light_level=light,
                                                special=sector_special,
                                            )
                                            if platform_kind in {"high_box_sector", "medium_box_sector"}:
                                                wall_tex = PLATFORM_CRATE_SIDE_TEXTURE_GRAY if use_gray_box_variant else PLATFORM_CRATE_SIDE_TEXTURE
                                            elif platform_kind == "low_box_sector":
                                                wall_tex = PLATFORM_BLOCKING_SIDE_TEXTURE
                                            else:
                                                wall_tex = theme.transition_wall_textures[0]
                                            for idx in range(len(vertex_indices)):
                                                v1 = vertex_indices[idx]
                                                v2 = vertex_indices[(idx + 1) % len(vertex_indices)]
                                                add_boundary_line(
                                                    map_data,
                                                    v1_idx=v1,
                                                    v2_idx=v2,
                                                    right_sector=detail_sector,
                                                    left_sector=room_sector,
                                                    right_wall_texture=wall_tex,
                                                    left_wall_texture=wall_tex,
                                                )
                                            placed_this_slot = True
                                            placed_total += 1
                                            placed_room_sector_area += one_cell_area
                                            seed_cell = CellXY(seed_ix, seed_iy)
                                            cell_state[seed_cell] = occupied_state
                                            for ox in (-1, 0, 1):
                                                for oy in (-1, 0, 1):
                                                    neighbor = CellXY(seed_ix + ox, seed_iy + oy)
                                                    if neighbor == seed_cell:
                                                        continue
                                                    if cell_state.get(neighbor) == free_state:
                                                        cell_state[neighbor] = buffer_state
                                            log_trace(
                                                f"SECTOR_PLACE_FALLBACK room={room_idx} kind={platform_kind} "
                                                f"cell=({seed_ix},{seed_iy}) floor={floor_h} ceil={ceil_h} special={sector_special}"
                                            )
                                            if platform_kind == "puddle_sector":
                                                placed_puddle_count += 1
                                            all_platform_local_polys_by_room.setdefault(room_idx, []).append(tuple(one_cell_local_poly))
                                            all_platform_world_polys.append(snapped_world_poly)
                                            if blocks_walk:
                                                blocked_local_polys_by_room.setdefault(room_idx, []).append(tuple(one_cell_local_poly))
                                            elif platform_kind == "puddle_sector":
                                                sunken_local_polys_by_room.setdefault(room_idx, []).append(tuple(one_cell_local_poly))

            if not placed_this_slot:
                log_trace(f"SECTOR_FAILURE room={room_idx} kind={platform_kind} attempts={MAX_RETRIES}")
                continue

        # *** PASS 5: Store outputs for this room (blocked/sunken masks, decor jobs, free-point pool) ***
        free_mask_local_points_by_room[room_idx] = [
            (float(ix) * cell_size, float(iy) * cell_size)
            for (ix, iy), state in cell_state.items()
            if state == free_state
        ]
    pool_state["placed_puddle_count"] = int(placed_puddle_count)

    return (
        placed_total,
        blocked_local_polys_by_room,
        sunken_local_polys_by_room,
        decor_jobs,
        all_platform_local_polys_by_room,
        free_mask_local_points_by_room,
    )


def place_internal_sector_decor(
    map_data: MutableMap,
    decor_jobs: list[tuple[tuple[tuple[float, float], ...], int]],
    theme_name: str,
    rng: random.Random,
    line_segments: list[tuple[tuple[float, float], tuple[float, float]]],
) -> None:
    if not decor_jobs:
        return
    decor_pool = SMALL_PLATFORM_DECOR_BY_THEME.get(theme_name, SMALL_PLATFORM_DECOR_BY_THEME["urban"])
    if not decor_pool:
        return
    spacing_sq = OBJECT_MIN_SPACING_UNITS * OBJECT_MIN_SPACING_UNITS
    edge_clearance_sq = OBJECT_MIN_SPACING_UNITS * OBJECT_MIN_SPACING_UNITS
    inset = 10.0

    for poly_world, decor_target in decor_jobs:
        if len(poly_world) < 3:
            continue
        xs = [point[0] for point in poly_world]
        ys = [point[1] for point in poly_world]
        min_wx = min(xs)
        max_wx = max(xs)
        min_wy = min(ys)
        max_wy = max(ys)
        if (max_wx - min_wx) < 20.0 or (max_wy - min_wy) < 20.0:
            continue

        placed_decor_points: list[tuple[float, float]] = []
        for decor_idx in range(1, decor_target + 1):
            for attempt_idx in range(1, MAX_RETRIES + 1):
                px = rng.uniform(min_wx + inset, max_wx - inset)
                py = rng.uniform(min_wy + inset, max_wy - inset)
                if not point_in_polygon((px, py), poly_world):
                    continue
                ix = int(round(px))
                iy = int(round(py))
                rounded_point = (float(ix), float(iy))
                if not point_in_polygon(rounded_point, poly_world):
                    continue
                if min_distance_to_polygon_edges_sq(rounded_point, poly_world) < edge_clearance_sq:
                    continue
                if any(
                    ((rounded_point[0] - qx) * (rounded_point[0] - qx) + (rounded_point[1] - qy) * (rounded_point[1] - qy)) < spacing_sq
                    for qx, qy in placed_decor_points
                ):
                    continue
                if add_object(
                    map_data,
                    ix,
                    iy,
                    rng.choice(decor_pool),
                    flags=7,
                    line_segments=line_segments,
                    min_spacing_units=OBJECT_MIN_SPACING_UNITS,
                ):
                    placed_decor_points.append(rounded_point)
                    break


def random_point_in_room(
    room: OrientedRoom,
    rng: random.Random,
    margin: float = 0.75,
    blocked_local_polys: list[tuple[tuple[float, float], ...]] | None = None,
    edge_clearance: float = 0.0,
) -> tuple[int, int]:
    blocked = blocked_local_polys or []
    edge_clearance_sq = edge_clearance * edge_clearance

    def local_point_is_valid(lx: float, ly: float) -> bool:
        if not point_in_room_local_shape(room, lx, ly):
            return False
        point = (lx, ly)
        if any(point_in_polygon(point, poly) for poly in blocked):
            return False
        if edge_clearance_sq > 0.0:
            for poly in blocked:
                if min_distance_to_polygon_edges_sq(point, poly) < edge_clearance_sq:
                    return False
        return True

    for _ in range(72):
        lx = rng.uniform(-room.half_length * margin, room.half_length * margin)
        ly = rng.uniform(-room.half_width * margin, room.half_width * margin)
        if not local_point_is_valid(lx, ly):
            continue
        wx, wy = local_to_world(room.center, room.tangent, room.normal, lx, ly)
        return int(round(wx)), int(round(wy))

    probe_points = (
        (0.0, 0.0),
        (room.half_length * margin * 0.35, 0.0),
        (-room.half_length * margin * 0.35, 0.0),
        (0.0, room.half_width * margin * 0.35),
        (0.0, -room.half_width * margin * 0.35),
        (room.half_length * margin * 0.25, room.half_width * margin * 0.25),
        (-room.half_length * margin * 0.25, room.half_width * margin * 0.25),
        (room.half_length * margin * 0.25, -room.half_width * margin * 0.25),
        (-room.half_length * margin * 0.25, -room.half_width * margin * 0.25),
    )
    for lx, ly in probe_points:
        if not local_point_is_valid(lx, ly):
            continue
        wx, wy = local_to_world(room.center, room.tangent, room.normal, lx, ly)
        return int(round(wx)), int(round(wy))

    for _ in range(180):
        lx = rng.uniform(-room.half_length * margin, room.half_length * margin)
        ly = rng.uniform(-room.half_width * margin, room.half_width * margin)
        if not local_point_is_valid(lx, ly):
            continue
        wx, wy = local_to_world(room.center, room.tangent, room.normal, lx, ly)
        return int(round(wx)), int(round(wy))

    for iy in range(-4, 5):
        for ix in range(-4, 5):
            lx = (ix / 4.0) * room.half_length * margin * 0.9
            ly = (iy / 4.0) * room.half_width * margin * 0.9
            if not local_point_is_valid(lx, ly):
                continue
            wx, wy = local_to_world(room.center, room.tangent, room.normal, lx, ly)
            return int(round(wx)), int(round(wy))

    wx, wy = local_to_world(room.center, room.tangent, room.normal, 0.0, 0.0)
    return int(round(wx)), int(round(wy))


def dead_end_room_indices(layout: PolyLayout) -> list[int]:
    degree = [0 for _ in layout.rooms]
    for a, b in layout.connections:
        if 0 <= a < len(degree):
            degree[a] += 1
        if 0 <= b < len(degree):
            degree[b] += 1
    return [idx for idx, deg in enumerate(degree) if idx != 0 and deg <= 1]


def opposite_room_on_edge(layout: PolyLayout, edge_idx: int, room_idx: int) -> int:
    if edge_idx < 0 or edge_idx >= len(layout.connections):
        return room_idx
    a, b = layout.connections[edge_idx]
    if room_idx == a:
        return b
    if room_idx == b:
        return a
    return room_idx


def select_exit_room_index(layout: PolyLayout) -> int:
    room_count = len(layout.rooms)
    # Strict campaign layouts reserve room 7 as the actual exit room:
    # 0->1->3->5->7 (with optional room 8 pass-through and optional bonus dead-end).
    if room_count in {8, 9, 10} and room_count > 7:
        return 7

    red_targets = [
        opposite_room_on_edge(layout, edge_idx, room_idx)
        for edge_idx, room_idx, color in layout.lock_sequence
        if color == "red"
    ]
    return red_targets[-1] if red_targets else -1


def room_sector_polygon(layout: PolyLayout, room_idx: int) -> tuple[tuple[float, float], ...]:
    seen = 0
    for plan in layout.sector_plans:
        if plan.kind != "room":
            continue
        if seen == room_idx:
            return plan.polygon
        seen += 1
    if 0 <= room_idx < len(layout.rooms):
        return layout.rooms[room_idx].polygon
    return tuple()


def preferred_start_anchor_poly(
    layout: PolyLayout,
    blocked_local_polys_by_room: dict[int, list[tuple[tuple[float, float], ...]]] | None = None,
    sunken_local_polys_by_room: dict[int, list[tuple[tuple[float, float], ...]]] | None = None,
) -> tuple[int, int, int]:
    if not layout.rooms:
        raise ValueError("No rooms in polygon layout for start anchor.")
    start_room = layout.rooms[0]
    start_room_poly = room_sector_polygon(layout, 0)
    start_angle = int(round(math.degrees(math.atan2(start_room.tangent[1], start_room.tangent[0])))) % 360
    start_blocked = list((blocked_local_polys_by_room or {}).get(0, []))
    start_blocked.extend((sunken_local_polys_by_room or {}).get(0, []))

    def start_spot_is_valid(lx: float, ly: float) -> bool:
        if any(point_in_polygon((lx, ly), poly) for poly in start_blocked):
            return False
        wx, wy = local_to_world(start_room.center, start_room.tangent, start_room.normal, lx, ly)
        if start_room_poly and not point_in_polygon((float(wx), float(wy)), start_room_poly):
            return False
        return True

    back_candidates = (
        max(-start_room.half_length + 104.0, -start_room.half_length * 0.72),
        max(-start_room.half_length + 148.0, -start_room.half_length * 0.58),
        max(-start_room.half_length + 196.0, -start_room.half_length * 0.45),
        -start_room.half_length * 0.30,
        0.0,
    )
    start_lx = 0.0
    for candidate_lx in back_candidates:
        if not start_spot_is_valid(candidate_lx, 0.0):
            continue
        start_lx = candidate_lx
        break

    if not start_spot_is_valid(start_lx, 0.0):
        for iy in range(-4, 5):
            found = False
            for ix in range(-6, 7):
                lx = (ix / 6.0) * start_room.half_length * 0.75
                ly = (iy / 4.0) * start_room.half_width * 0.75
                if not start_spot_is_valid(lx, ly):
                    continue
                start_lx = lx
                start_ly = ly
                found = True
                break
            if found:
                break
        else:
            start_ly = 0.0
    else:
        start_ly = 0.0
    start_wx, start_wy = local_to_world(start_room.center, start_room.tangent, start_room.normal, start_lx, start_ly)
    return int(round(start_wx)), int(round(start_wy)), start_angle


def add_map_objects(
    map_data: MutableMap,
    layout: PolyLayout,
    spec: EpisodeMapSpec,
    rng: random.Random,
    monster_rng: random.Random | None = None,
    population_targets: MapPopulationTargets | None = None,
    blocked_local_polys_by_room: dict[int, list[tuple[tuple[float, float], ...]]] | None = None,
    sunken_local_polys_by_room: dict[int, list[tuple[tuple[float, float], ...]]] | None = None,
    platform_local_polys_by_room: dict[int, list[tuple[tuple[float, float], ...]]] | None = None,
    room_free_mask_local_points_by_room: dict[int, list[tuple[float, float]]] | None = None,
) -> tuple[int, int]:
    if not layout.rooms:
        raise ValueError(f"{spec.output_map}: no rooms in polygon layout.")
    map_num = map_number_from_name(spec.output_map) or 1
    if monster_rng is None:
        monster_rng = rng

    targets = population_targets or MapPopulationTargets(
        rooms=list(range(len(layout.rooms))),
        platforms=[],
        corridors=list(range(len(layout.corridors))),
    )
    non_walkable_world_polys: list[tuple[tuple[float, float], ...]] = []
    for plan in layout.sector_plans:
        if len(plan.polygon) < 3:
            continue
        headroom = plan.ceiling_height - plan.floor_height
        if headroom < OBJECT_MIN_HEADROOM_UNITS:
            non_walkable_world_polys.append(plan.polygon)
    if targets.platforms:
        place_internal_sector_decor(
            map_data,
            targets.platforms,
            spec.theme,
            rng,
            collect_line_segments(map_data, edge_only=True),
        )
    line_segments = collect_line_segments(map_data, edge_only=True)

    min_spacing_sq = OBJECT_MIN_SPACING_UNITS * OBJECT_MIN_SPACING_UNITS
    placed_object_points: list[tuple[float, float]] = [
        (float(thing.x), float(thing.y)) for thing in map_data.things
    ]

    def is_spot_clear(x: int, y: int) -> bool:
        xf = float(x)
        yf = float(y)
        return not any(((xf - px) * (xf - px) + (yf - py) * (yf - py)) < min_spacing_sq for px, py in placed_object_points)

    def record_spot(x: int, y: int) -> None:
        placed_object_points.append((float(x), float(y)))

    def room_item_blocked(room_idx: int) -> list[tuple[tuple[float, float], ...]]:
        blocked = list((platform_local_polys_by_room or {}).get(room_idx, []))
        blocked.extend((blocked_local_polys_by_room or {}).get(room_idx, []))
        blocked.extend((sunken_local_polys_by_room or {}).get(room_idx, []))
        return blocked

    room_poly_cache: dict[int, tuple[tuple[float, float], ...]] = {
        idx: room_sector_polygon(layout, idx) for idx in range(len(layout.rooms))
    }
    room_blocked_cache: dict[int, list[tuple[tuple[float, float], ...]]] = {
        idx: room_item_blocked(idx) for idx in range(len(layout.rooms))
    }
    room_candidate_cache: dict[int, list[tuple[int, int, float, float]]] = {}

    def build_room_candidate_pool(room_idx: int) -> list[tuple[int, int, float, float]]:
        if room_idx in room_candidate_cache:
            return room_candidate_cache[room_idx]
        if room_idx < 0 or room_idx >= len(layout.rooms):
            room_candidate_cache[room_idx] = []
            return []

        room = layout.rooms[room_idx]
        room_poly = room_poly_cache.get(room_idx, tuple())
        blocked = room_blocked_cache.get(room_idx, [])
        edge_clearance_sq = OBJECT_MIN_SPACING_UNITS * OBJECT_MIN_SPACING_UNITS
        grid_step = max(8.0, float(OBJECT_POOL_GRID_STEP_UNITS))
        points: list[tuple[int, int, float, float]] = []
        seen_world: set[tuple[int, int]] = set()
        masked_seeds = (room_free_mask_local_points_by_room or {}).get(room_idx, [])
        if masked_seeds:
            sub_step = max(8.0, min(float(OBJECT_MIN_SPACING_UNITS) * 0.5, float(PLATFORM_EDGE_UNITS) * 0.25))
            offsets = [
                (-sub_step, -sub_step), (-sub_step, 0.0), (-sub_step, sub_step),
                (0.0, -sub_step), (0.0, 0.0), (0.0, sub_step),
                (sub_step, -sub_step), (sub_step, 0.0), (sub_step, sub_step),
            ]
            candidate_locals = [
                (sx + ox, sy + oy)
                for sx, sy in masked_seeds
                for ox, oy in offsets
            ]
        else:
            nx = max(1, int(math.ceil(room.half_length / grid_step)))
            ny = max(1, int(math.ceil(room.half_width / grid_step)))
            candidate_locals = [
                (float(ix) * grid_step, float(iy) * grid_step)
                for iy in range(-ny, ny + 1)
                for ix in range(-nx, nx + 1)
            ]

        for lx, ly in candidate_locals:
            if not point_in_room_local_shape(room, lx, ly):
                continue
            local_point = (lx, ly)
            if any(point_in_polygon(local_point, poly) for poly in blocked):
                continue
            if any(min_distance_to_polygon_edges_sq(local_point, poly) < edge_clearance_sq for poly in blocked):
                continue
            wx, wy = local_to_world(room.center, room.tangent, room.normal, lx, ly)
            px = int(round(wx))
            py = int(round(wy))
            world_key = (px, py)
            if world_key in seen_world:
                continue
            world_point = (float(px), float(py))
            if room_poly and not point_in_polygon(world_point, room_poly):
                continue
            if any(point_in_polygon(world_point, poly) for poly in non_walkable_world_polys):
                continue
            if not point_clear_of_lines(world_point, line_segments, OBJECT_MIN_SPACING_UNITS):
                continue
            seen_world.add(world_key)
            points.append((px, py, lx, ly))

        room_candidate_cache[room_idx] = points
        log_trace(f"ROOM_CANDIDATE_POOL room={room_idx} size={len(points)}")
        return points

    def room_point_picker_from_pool(
        room_idx: int,
        margin: float,
        blocked_local_polys: list[tuple[tuple[float, float], ...]],
    ):
        room = layout.rooms[room_idx]
        margin_x = room.half_length * float(margin)
        margin_y = room.half_width * float(margin)

        def picker() -> tuple[int, int]:
            pool = build_room_candidate_pool(room_idx)
            for _ in range(max(12, len(pool) // 6)):
                if not pool:
                    break
                px, py, lx, ly = rng.choice(pool)
                if abs(lx) > margin_x or abs(ly) > margin_y:
                    continue
                if any(point_in_polygon((lx, ly), poly) for poly in blocked_local_polys):
                    continue
                return (px, py)
            return random_point_in_room(
                room,
                rng,
                margin=margin,
                blocked_local_polys=blocked_local_polys,
                edge_clearance=OBJECT_MIN_SPACING_UNITS,
            )

        return picker

    room_parent: list[int] = [-1 for _ in layout.rooms]
    room_depth: list[int] = [10**9 for _ in layout.rooms]
    if layout.rooms:
        adjacency: list[list[int]] = [[] for _ in layout.rooms]
        for a, b in layout.connections:
            if 0 <= a < len(adjacency) and 0 <= b < len(adjacency):
                adjacency[a].append(b)
                adjacency[b].append(a)
        queue: deque[int] = deque([0])
        seen = {0}
        room_depth[0] = 0
        while queue:
            node = queue.popleft()
            for nxt in adjacency[node]:
                if nxt in seen:
                    continue
                seen.add(nxt)
                room_parent[nxt] = node
                room_depth[nxt] = room_depth[node] + 1
                queue.append(nxt)

    def facing_angle_toward(x: int, y: int, tx: float, ty: float, *, jitter: float = 40.0) -> int:
        base = math.degrees(math.atan2(ty - float(y), tx - float(x)))
        return int(round((base + rng.uniform(-jitter, jitter)) % 360.0))

    def facing_angle_away_from_entry(x: int, y: int, tx: float, ty: float) -> int:
        base = math.degrees(math.atan2(ty - float(y), tx - float(x)))
        return int(round((base + 180.0 + rng.uniform(-60.0, 60.0)) % 360.0))

    def expected_entry_target(room_idx: int) -> tuple[float, float] | None:
        if room_idx <= 0 or room_idx >= len(layout.rooms):
            return None
        parent_idx = room_parent[room_idx]
        if parent_idx < 0 or parent_idx >= len(layout.rooms):
            return None
        room = layout.rooms[room_idx]
        parent_center = layout.rooms[parent_idx].center
        parent_dir = v_norm(v_sub(parent_center, room.center))
        candidate_sides = layout.room_door_sides[room_idx] if room_idx < len(layout.room_door_sides) else ()
        if candidate_sides:
            best_side = max(candidate_sides, key=lambda side: v_dot(room_side_forward(room, side), parent_dir))
            outward = room_side_forward(room, best_side)
            return (
                room.center[0] + outward[0] * room.half_length,
                room.center[1] + outward[1] * room.half_width,
            )
        return parent_center

    def place_thing_spaced(
        thing_type: int,
        point_picker,
        *,
        flags: int = 7,
        angle: int = 0,
        angle_picker=None,
        attempts: int = 48,
        force: bool = False,
        min_spacing_units: float = OBJECT_MIN_SPACING_UNITS,
    ) -> bool:
        last_point: tuple[int, int] | None = None
        total_attempts = max(1, attempts)
        for attempt_idx in range(1, total_attempts + 1):
            x, y = point_picker()
            last_point = (x, y)
            if not is_spot_clear(x, y):
                continue
            placed_angle = int(angle_picker(x, y)) if angle_picker is not None else int(angle)
            if add_object(
                map_data,
                x,
                y,
                thing_type,
                angle=placed_angle,
                flags=flags,
                line_segments=line_segments,
                min_spacing_units=min_spacing_units,
                non_walkable_polys=non_walkable_world_polys,
            ):
                record_spot(x, y)
                return True

        if force and last_point is not None:
            x, y = last_point
            placed_angle = int(angle_picker(x, y)) if angle_picker is not None else int(angle)
            if add_object(
                map_data,
                x,
                y,
                thing_type,
                angle=placed_angle,
                flags=flags,
                line_segments=line_segments,
                min_spacing_units=min_spacing_units,
                non_walkable_polys=non_walkable_world_polys,
            ):
                record_spot(x, y)
                return True
        return False

    start_room = layout.rooms[0]
    start_room_poly = room_sector_polygon(layout, 0)
    start_x, start_y, start_angle = preferred_start_anchor_poly(
        layout,
        blocked_local_polys_by_room=blocked_local_polys_by_room,
        sunken_local_polys_by_room=sunken_local_polys_by_room,
    )
    start_blocked = room_blocked_cache.get(0, [])
    start_room_pool_picker = room_point_picker_from_pool(0, 0.58, start_blocked)

    def world_start_spot_is_clear(wx: int, wy: int) -> bool:
        if start_room_poly and not point_in_polygon((float(wx), float(wy)), start_room_poly):
            return False
        dx = float(wx) - start_room.center[0]
        dy = float(wy) - start_room.center[1]
        lx = (dx * start_room.tangent[0]) + (dy * start_room.tangent[1])
        ly = (dx * start_room.normal[0]) + (dy * start_room.normal[1])
        if any(point_in_polygon((lx, ly), poly) for poly in start_blocked):
            return False
        return is_spot_clear(wx, wy)

    def random_point_in_start_room_polygon() -> tuple[int, int]:
        for attempt_idx in range(1, MAX_RETRIES + 1):
            wx, wy = start_room_pool_picker()
            if world_start_spot_is_clear(wx, wy):
                return wx, wy
        return start_x, start_y

    def try_place_start_grid(thing_type: int, spacing_units: float) -> bool:
        for iy in range(-10, 11):
            for ix in range(-12, 13):
                lx = (ix / 12.0) * start_room.half_length * 0.78
                ly = (iy / 10.0) * start_room.half_width * 0.78
                wx, wy = local_to_world(start_room.center, start_room.tangent, start_room.normal, lx, ly)
                px = int(round(wx))
                py = int(round(wy))
                if not world_start_spot_is_clear(px, py):
                    continue
                if add_object(
                    map_data,
                    px,
                    py,
                    thing_type,
                    angle=start_angle,
                    flags=7,
                    line_segments=line_segments,
                    min_spacing_units=spacing_units,
                    non_walkable_polys=non_walkable_world_polys,
                ):
                    record_spot(px, py)
                    return True
        return False

    def place_start_player(thing_type: int, pref_x: int, pref_y: int) -> None:
        placed = False
        if world_start_spot_is_clear(pref_x, pref_y):
            placed = place_thing_spaced(
                thing_type,
                point_picker=lambda x=pref_x, y=pref_y: (x, y),
                angle=start_angle,
                flags=7,
                attempts=1,
            )
        if not placed:
            placed = place_thing_spaced(
                thing_type,
                point_picker=random_point_in_start_room_polygon,
                angle=start_angle,
                flags=7,
                attempts=MAX_RETRIES,
            )
        if not placed:
            placed = try_place_start_grid(thing_type, OBJECT_MIN_SPACING_UNITS)
        if not placed and thing_type == 1:
            for relaxed_spacing in (24.0, 16.0, 8.0, 0.0):
                if try_place_start_grid(thing_type, relaxed_spacing):
                    if relaxed_spacing < OBJECT_MIN_SPACING_UNITS:
                        print(f"INFO: player1 start placed with relaxed spacing ({relaxed_spacing:.1f}).")
                    placed = True
                    break
        if not placed and thing_type == 1:
            add_object(
                map_data,
                start_x,
                start_y,
                1,
                angle=start_angle,
                flags=7,
                line_segments=None,
                min_spacing_units=0.0,
            )
            record_spot(start_x, start_y)
            print("INFO: player1 start placed with emergency fallback.")

    place_start_player(1, start_x, start_y)
    place_start_player(2, start_x - 40, start_y - 24)
    place_start_player(3, start_x - 80, start_y + 24)
    place_start_player(4, start_x - 120, start_y)

    room_indices = [idx for idx in targets.rooms if 0 <= idx < len(layout.rooms)]

    decor_pool = DECOR_POOL_BY_THEME.get(spec.theme, DECOR_POOL_BY_THEME["urban"])

    def add_map_monsters(
        room_idx: int,
        room: OrientedRoom,
        blocked: list[tuple[tuple[float, float], ...]],
        cover_polys: list[tuple[tuple[float, float], ...]],
        entry_target: tuple[float, float] | None,
        *,
        force_all_deaf: bool = False,
    ) -> None:
        def local_spawn_valid(lx: float, ly: float, edge_clearance_sq: float) -> bool:
            point = (lx, ly)
            if not point_in_room_local_shape(room, lx, ly):
                return False
            if any(point_in_polygon(point, poly) for poly in blocked):
                return False
            for poly in blocked:
                if min_distance_to_polygon_edges_sq(point, poly) < edge_clearance_sq:
                    return False
            return True

        def room_monster_picker(monster_clearance: float) -> tuple[int, int]:
            return random_point_in_room(
                room,
                rng,
                margin=0.72,
                blocked_local_polys=blocked,
                edge_clearance=monster_clearance,
            )

        def random_point_behind_cover(monster_clearance: float) -> tuple[int, int]:
            if not cover_polys or entry_target is None:
                return room_monster_picker(monster_clearance)

            edge_clearance_sq = float(monster_clearance) * float(monster_clearance)

            tx, ty = entry_target
            dx = float(tx) - room.center[0]
            dy = float(ty) - room.center[1]
            entry_lx = (dx * room.tangent[0]) + (dy * room.tangent[1])
            entry_ly = (dx * room.normal[0]) + (dy * room.normal[1])

            for _ in range(72):
                poly = rng.choice(cover_polys)
                if len(poly) < 3:
                    continue
                cx = sum(p[0] for p in poly) / float(len(poly))
                cy = sum(p[1] for p in poly) / float(len(poly))
                vx = cx - entry_lx
                vy = cy - entry_ly
                mag = math.hypot(vx, vy)
                if mag <= 1.0e-6:
                    angle = rng.uniform(0.0, math.tau)
                    ux = math.cos(angle)
                    uy = math.sin(angle)
                else:
                    ux = vx / mag
                    uy = vy / mag
                px = cx + (ux * rng.uniform(56.0, 120.0)) + ((-uy) * rng.uniform(-40.0, 40.0))
                py = cy + (uy * rng.uniform(56.0, 120.0)) + (ux * rng.uniform(-40.0, 40.0))
                if not local_spawn_valid(px, py, edge_clearance_sq):
                    continue
                wx, wy = local_to_world(room.center, room.tangent, room.normal, px, py)
                return int(round(wx)), int(round(wy))

            return room_monster_picker(monster_clearance)

        spawn_count = rng.randint(
            int(ROOM_MONSTER_BASE_MIN + map_num * ROOM_MONSTER_SCALE),
            int(ROOM_MONSTER_BASE_MAX + map_num * ROOM_MONSTER_SCALE),
        )
        for _ in range(spawn_count):
            is_deaf = bool(force_all_deaf) or (monster_rng.random() < MONSTER_DEAF_CHANCE)
            monster_flags = 7 | (THING_FLAG_AMBUSH if is_deaf else 0)
            monster_type = weighted_pick(
                pick_tier_table_by_map_number(map_num, ROOM_MONSTER_WEIGHTS_BY_TIER, monster_rng),
                monster_rng,
            )
            monster_clearance = monster_spawn_clearance_units(monster_type)
            angle_picker = None
            if entry_target is not None:
                tx, ty = entry_target
                angle_picker = lambda x, y, tx=tx, ty=ty: facing_angle_toward(x, y, tx, ty, jitter=45.0)
            point_picker = (
                (lambda clearance=monster_clearance: random_point_behind_cover(clearance))
                if is_deaf
                else (lambda clearance=monster_clearance: room_monster_picker(clearance))
            )
            place_thing_spaced(
                thing_type=monster_type,
                angle=monster_rng.choice((0, 45, 90, 135, 180, 225, 270, 315)),
                angle_picker=angle_picker,
                point_picker=point_picker,
                flags=monster_flags,
                attempts=72,
                min_spacing_units=monster_clearance,
            )

    def add_map_pickups(
        room_idx: int,
        item_blocked: list[tuple[tuple[float, float], ...]],
    ) -> None:
        pickup_picker_55 = room_point_picker_from_pool(room_idx, 0.55, item_blocked)
        pickup_picker_60 = room_point_picker_from_pool(room_idx, 0.60, item_blocked)
        pickup_picker_62 = room_point_picker_from_pool(room_idx, 0.62, item_blocked)
        roll_count = rng.randint(
            int(ROOM_ITEM_BASE_MIN + map_num * ROOM_ITEM_SCALE),
            int(ROOM_ITEM_BASE_MAX + map_num * ROOM_ITEM_SCALE),
        )
        point_pickers = (pickup_picker_55, pickup_picker_60, pickup_picker_62)
        for idx in range(roll_count):
            room_pickup_weights = pick_tier_table_by_map_number(map_num, ROOM_PICKUP_TABLE_BY_TIER, rng)
            pickup_type = weighted_pick(room_pickup_weights, rng)
            if pickup_type <= 0:
                continue
            place_thing_spaced(
                pickup_type,
                point_picker=point_pickers[min(idx, len(point_pickers) - 1)],
                flags=7,
                attempts=60,
            )

    def add_map_decorations(
        room_idx: int,
        room: OrientedRoom,
        item_blocked: list[tuple[tuple[float, float], ...]],
    ) -> None:
        decor_picker = room_point_picker_from_pool(room_idx, 0.58, item_blocked)
        base_decor_count = rng.randint(2, 4)
        room_poly = room_sector_polygon(layout, room_idx)
        room_area = polygon_area_abs(room_poly)
        if room_area <= 0.0:
            room_area = (2.0 * room.half_length) * (2.0 * room.half_width)
        decor_scale = max(0.6, min(3.0, room_area / 360000.0))
        decor_count = stochastic_scaled_count(base_decor_count, decor_scale, rng, minimum=1)
        decor_count = min(14, decor_count)
        for _ in range(decor_count):
            place_thing_spaced(
                rng.choice(decor_pool),
                point_picker=decor_picker,
                flags=7,
                attempts=60,
            )

    def key_world_spot_is_valid(
        room_idx: int,
        room: OrientedRoom,
        blocked_local_polys: list[tuple[tuple[float, float], ...]],
        wx: int,
        wy: int,
    ) -> bool:
        world_point = (float(wx), float(wy))
        room_poly = room_poly_cache.get(room_idx, tuple())
        if room_poly and not point_in_polygon(world_point, room_poly):
            return False
        dx = float(wx) - room.center[0]
        dy = float(wy) - room.center[1]
        lx = (dx * room.tangent[0]) + (dy * room.tangent[1])
        ly = (dx * room.normal[0]) + (dy * room.normal[1])
        if any(point_in_polygon((lx, ly), poly) for poly in blocked_local_polys):
            return False
        if any(point_in_polygon(world_point, poly) for poly in non_walkable_world_polys):
            return False
        if not is_spot_clear(wx, wy):
            return False
        return True

    def place_key_guaranteed(room_idx: int, thing_type: int) -> None:
        room = layout.rooms[room_idx]
        blocked = room_item_blocked(room_idx)
        key_picker = room_point_picker_from_pool(room_idx, 0.45, blocked)
        placed = place_thing_spaced(
            thing_type,
            point_picker=key_picker,
            flags=7,
            attempts=140,
            force=True,
        )
        if placed:
            return

        # Progressive fallback: relax spacing/line checks while still forcing in-room placement.
        for spacing in (OBJECT_MIN_SPACING_UNITS, 24.0, 16.0, 8.0, 0.0):
            for _ in range(160):
                px, py = key_picker()
                if not key_world_spot_is_valid(room_idx, room, blocked, px, py):
                    continue
                if add_object(
                    map_data,
                    px,
                    py,
                    thing_type,
                    angle=0,
                    flags=7,
                    line_segments=line_segments if spacing > 0.0 else None,
                    min_spacing_units=spacing,
                    non_walkable_polys=non_walkable_world_polys if spacing > 0.0 else None,
                ):
                    record_spot(px, py)
                    print(
                        f"INFO: key {thing_type} placed with fallback "
                        f"(room={room_idx}, spacing={spacing:.1f})."
                    )
                    return

        # Deterministic in-room sweep before emergency placement.
        for spacing in (16.0, 8.0, 0.0):
            for iy in range(-10, 11):
                for ix in range(-12, 13):
                    lx = (ix / 12.0) * room.half_length * 0.86
                    ly = (iy / 10.0) * room.half_width * 0.86
                    wx, wy = local_to_world(room.center, room.tangent, room.normal, lx, ly)
                    px = int(round(wx))
                    py = int(round(wy))
                    if not key_world_spot_is_valid(room_idx, room, blocked, px, py):
                        continue
                    if add_object(
                        map_data,
                        px,
                        py,
                        thing_type,
                        angle=0,
                        flags=7,
                        line_segments=line_segments if spacing > 0.0 else None,
                        min_spacing_units=spacing,
                        non_walkable_polys=non_walkable_world_polys if spacing > 0.0 else None,
                    ):
                        record_spot(px, py)
                        print(
                            f"INFO: key {thing_type} placed with grid fallback "
                            f"(room={room_idx}, spacing={spacing:.1f})."
                        )
                        return

        # Hard guarantee fallback: place near room center with minimal constraints.
        cx, cy = local_to_world(room.center, room.tangent, room.normal, 0.0, 0.0)
        ex = int(round(cx))
        ey = int(round(cy))
        add_object(
            map_data,
            ex,
            ey,
            thing_type,
            angle=0,
            flags=7,
            line_segments=None,
            min_spacing_units=0.0,
            non_walkable_polys=None,
        )
        record_spot(ex, ey)
        print(f"INFO: key {thing_type} placed with emergency fallback (room={room_idx}).")

    # Progression-critical items go first so regular room population cannot crowd them out.
    for room_idx, color in layout.key_sequence:
        if room_idx <= 0 or room_idx >= len(layout.rooms):
            continue
        thing_type = KEY_THING_BY_COLOR.get(color)
        if thing_type is None:
            continue
        place_key_guaranteed(room_idx, thing_type)

    for room_idx in room_indices:
        room = layout.rooms[room_idx]
        blocked = room_item_blocked(room_idx)
        cover_polys = list((blocked_local_polys_by_room or {}).get(room_idx, []))
        item_blocked = room_item_blocked(room_idx)
        entry_target = expected_entry_target(room_idx)
        if entry_target is None and room_idx == 0:
            entry_target = (float(start_x), float(start_y))
        add_map_monsters(
            room_idx,
            room,
            blocked,
            cover_polys,
            entry_target,
        )
        add_map_pickups(room_idx, item_blocked)
        add_map_decorations(room_idx, room, item_blocked)

    barrel_indices = list(range(2, len(layout.rooms)))
    shuffled = barrel_indices[:]
    rng.shuffle(shuffled)
    barrel_room_count = min(len(shuffled), max(2, len(layout.rooms) // 5))
    for room_idx in shuffled[:barrel_room_count]:
        room = layout.rooms[room_idx]
        blocked = room_item_blocked(room_idx)
        barrel_picker = room_point_picker_from_pool(room_idx, 0.48, blocked)
        barrel_count = rng.randint(2, 5)
        for _ in range(barrel_count):
            place_thing_spaced(
                2035,
                point_picker=barrel_picker,
                flags=7,
                attempts=60,
            )

    corridor_points: list[tuple[float, float]] = []
    corridor_monster_points: list[tuple[tuple[float, float], tuple[float, float]]] = []
    corridor_pickup_points: list[tuple[float, float]] = []
    corridor_monster_points_by_corridor: list[list[tuple[tuple[float, float], tuple[float, float]]]] = []
    corridor_pickup_points_by_corridor: list[list[tuple[float, float]]] = []
    corridor_raw_points: list[tuple[float, float]] = []
    corridor_raw_monster_points: list[tuple[tuple[float, float], tuple[float, float]]] = []
    corridor_raw_pickup_points: list[tuple[float, float]] = []

    def corridor_point_is_valid(px: float, py: float) -> bool:
        point = (float(int(round(px))), float(int(round(py))))
        return point_clear_of_lines(point, line_segments, OBJECT_MIN_SPACING_UNITS)

    corridor_indices = [idx for idx in targets.corridors if 0 <= idx < len(layout.corridors)]
    for corridor_idx in corridor_indices:
        corridor = layout.corridors[corridor_idx]
        entry_anchor = corridor.sections[0].center
        if corridor_idx < len(layout.connections):
            room_a_idx, room_b_idx = layout.connections[corridor_idx]
            if 0 <= room_a_idx < len(room_depth) and 0 <= room_b_idx < len(room_depth):
                if room_depth[room_a_idx] <= room_depth[room_b_idx]:
                    entry_anchor = corridor.sections[0].center
                else:
                    entry_anchor = corridor.sections[-1].center
        seen_filtered: set[tuple[int, int]] = set()
        seen_raw: set[tuple[int, int]] = set()
        local_points: list[tuple[float, float]] = []
        local_monster_points: list[tuple[tuple[float, float], tuple[float, float]]] = []
        local_raw_points: list[tuple[float, float]] = []
        local_raw_monster_points: list[tuple[tuple[float, float], tuple[float, float]]] = []
        local_pickup_points: list[tuple[float, float]] = []
        local_raw_pickup_points: list[tuple[float, float]] = []
        for section in corridor.sections[1:-1]:
            cx, cy = section.center
            raw_key = (int(round(cx)), int(round(cy)))
            if raw_key not in seen_raw:
                seen_raw.add(raw_key)
                local_raw_points.append((cx, cy))
                local_raw_monster_points.append(((cx, cy), entry_anchor))

            lx, ly = section.left
            rx, ry = section.right

            sample_ts = (0.35, 0.5, 0.65)
            for t in sample_ts:
                px = lx + ((rx - lx) * t)
                py = ly + ((ry - ly) * t)
                key = (int(round(px)), int(round(py)))
                if key in seen_filtered:
                    continue
                if not corridor_point_is_valid(px, py):
                    continue
                seen_filtered.add(key)
                local_points.append((px, py))
                local_monster_points.append(((px, py), entry_anchor))

        # Pickups: exactly one candidate per corridor sector (between adjacent
        # cross-sections), placed at that sector's geometric midpoint and still
        # centered between side walls.
        for seg_idx in range(len(corridor.sections) - 1):
            sec_a = corridor.sections[seg_idx]
            sec_b = corridor.sections[seg_idx + 1]
            left_mid_x = (sec_a.left[0] + sec_b.left[0]) * 0.5
            left_mid_y = (sec_a.left[1] + sec_b.left[1]) * 0.5
            right_mid_x = (sec_a.right[0] + sec_b.right[0]) * 0.5
            right_mid_y = (sec_a.right[1] + sec_b.right[1]) * 0.5
            mx = (left_mid_x + right_mid_x) * 0.5
            my = (left_mid_y + right_mid_y) * 0.5
            local_raw_pickup_points.append((mx, my))
            if corridor_point_is_valid(mx, my):
                local_pickup_points.append((mx, my))

        if len(local_points) < max(2, len(local_raw_points) // 6):
            local_points = local_raw_points[:]
            local_monster_points = local_raw_monster_points[:]
        if len(local_pickup_points) < max(2, len(local_raw_pickup_points) // 6):
            local_pickup_points = local_raw_pickup_points[:]

        corridor_points.extend(local_points)
        corridor_monster_points.extend(local_monster_points)
        corridor_pickup_points.extend(local_pickup_points)
        corridor_raw_points.extend(local_raw_points)
        corridor_raw_monster_points.extend(local_raw_monster_points)
        corridor_raw_pickup_points.extend(local_raw_pickup_points)
        corridor_monster_points_by_corridor.append(local_monster_points)
        corridor_pickup_points_by_corridor.append(local_pickup_points)

    log_trace(
        f"CORRIDOR_POOL final={len(corridor_points)} raw={len(corridor_raw_points)}"
    )
    log_trace(
        f"CORRIDOR_PICKUP_POOL final={len(corridor_pickup_points)} raw={len(corridor_raw_pickup_points)}"
    )

    start_cx, start_cy = start_room.center
    for points_for_corridor in corridor_monster_points_by_corridor:
        if not points_for_corridor:
            continue
        monster_points = [
            entry
            for entry in points_for_corridor
            if ((entry[0][0] - start_cx) ** 2 + (entry[0][1] - start_cy) ** 2) >= (256.0 * 256.0)
        ]
        if not monster_points:
            monster_points = points_for_corridor

        corridor_monster_count = rng.randint(
            int(CORRIDOR_MONSTER_BASE_MIN + map_num * CORRIDOR_MONSTER_SCALE),
            int(CORRIDOR_MONSTER_BASE_MAX + map_num * CORRIDOR_MONSTER_SCALE),
        )
        for _ in range(corridor_monster_count):
            (base_px, base_py), (tx, ty) = monster_rng.choice(monster_points)
            is_deaf = monster_rng.random() < MONSTER_DEAF_CHANCE
            monster_flags = 7 | (THING_FLAG_AMBUSH if is_deaf else 0)
            place_thing_spaced(
                weighted_pick(CORRIDOR_MONSTER_WEIGHTS, monster_rng),
                point_picker=lambda px=base_px, py=base_py: (
                    int(round(px)),
                    int(round(py)),
                ),
                angle=monster_rng.choice((0, 45, 90, 135, 180, 225, 270, 315)),
                angle_picker=lambda x, y, tx=tx, ty=ty: facing_angle_toward(
                    x,
                    y,
                    tx,
                    ty,
                    jitter=45.0,
                ),
                flags=monster_flags,
                attempts=64,
            )

    def place_corridor_pickup(thing_type: int, pickup_points_available: list[tuple[float, float]]) -> bool:
        if not pickup_points_available:
            return False

        candidates = pickup_points_available[:]
        rng.shuffle(candidates)
        attempts = 72 if thing_type in {2014, 2015} else 56
        for px, py in candidates:
            placed = place_thing_spaced(
                thing_type,
                point_picker=lambda x=px, y=py: (int(round(x)), int(round(y))),
                flags=7,
                attempts=1,
            )
            if placed:
                pickup_points_available.remove((px, py))
                return True
            attempts -= 1
            if attempts <= 0:
                break
        return False

    for points_for_corridor in corridor_pickup_points_by_corridor:
        corridor_pickup_points_available = points_for_corridor[:]
        if not corridor_pickup_points_available:
            continue
        corridor_item_count = rng.randint(
            int(CORRIDOR_ITEM_BASE_MIN + map_num * CORRIDOR_ITEM_SCALE),
            int(CORRIDOR_ITEM_BASE_MAX + map_num * CORRIDOR_ITEM_SCALE),
        )
        corridor_item_count = min(
            len(corridor_pickup_points_available),
            corridor_item_count,
        )
        for _ in range(corridor_item_count):
            corridor_pickup_table = pick_tier_table_by_map_number(map_num, CORRIDOR_PICKUP_TABLE_BY_TIER, rng)
            corridor_pickup_weights = [(thing_type, weight) for thing_type, weight in corridor_pickup_table if weight > 0]
            if not corridor_pickup_weights:
                continue
            pickup_type = weighted_pick(corridor_pickup_weights, rng)
            if pickup_type <= 0:
                continue
            place_corridor_pickup(pickup_type, corridor_pickup_points_available)

    exit_room_idx = select_exit_room_index(layout)
    key_rooms = {room_idx for room_idx, _color in layout.key_sequence}
    dead_ends = dead_end_room_indices(layout)
    treasure_candidates = [idx for idx in dead_ends if idx not in key_rooms and idx != exit_room_idx]
    if len(layout.rooms) == 10:
        treasure_room_idx = 9
    elif len(layout.rooms) == 9:
        treasure_room_idx = 8
    else:
        treasure_room_idx = min(treasure_candidates) if treasure_candidates else -1

    for room_idx in dead_ends:
        if room_idx != treasure_room_idx:
            continue  # Only the treasure room gets the special dead-end drop table.
        reward_type = weighted_pick(TREASURE_ROOM_REWARD_WEIGHTS, rng)
        blocked = room_item_blocked(room_idx)
        reward_picker = room_point_picker_from_pool(room_idx, 0.42, blocked)
        place_thing_spaced(
            reward_type,
            point_picker=reward_picker,
            flags=7,
            attempts=96,
        )

    return start_x, start_y


def populate_things_poly(
    map_data: MutableMap,
    layout: PolyLayout,
    spec: EpisodeMapSpec,
    rng: random.Random,
    blocked_local_polys_by_room: dict[int, list[tuple[tuple[float, float], ...]]] | None = None,
    sunken_local_polys_by_room: dict[int, list[tuple[tuple[float, float], ...]]] | None = None,
    platform_local_polys_by_room: dict[int, list[tuple[tuple[float, float], ...]]] | None = None,
) -> tuple[int, int]:
    return add_map_objects(
        map_data,
        layout,
        spec,
        rng,
        population_targets=None,
        blocked_local_polys_by_room=blocked_local_polys_by_room,
        sunken_local_polys_by_room=sunken_local_polys_by_room,
        platform_local_polys_by_room=platform_local_polys_by_room,
    )


def counts_for_poly_report(
    layout: PolyLayout,
    map_data: MutableMap,
    theme: ThemeStyle,
) -> tuple[int, int, int, int, int]:
    corridor_sectors = sum(1 for plan in layout.sector_plans if plan.kind == "corridor")
    corridor_floor_levels = {
        sector.floor_height
        for sector in map_data.sectors
        if sector.floor_texture == theme.corridor_floor
    }
    return (
        len(layout.rooms),
        corridor_sectors,
        len(map_data.things),
        len(map_data.linedefs),
        len(corridor_floor_levels),
    )


def udmf_escape(value: str) -> str:
    return value.replace("\\", "\\\\").replace('"', '\\"')


def udmf_bool(name: str, value: bool) -> str:
    return f"    {name} = {'true' if value else 'false'};\n"


def stochastic_scaled_count(base: int, multiplier: float, rng: random.Random, minimum: int = 0) -> int:
    scaled = float(base) * float(multiplier)
    whole = int(math.floor(scaled))
    frac = scaled - float(whole)
    if rng.random() < frac:
        whole += 1
    return max(minimum, whole)


def random_corridor_light(base_light: int, rng: random.Random) -> int:
    factor = rng.uniform(CORRIDOR_LIGHT_FACTOR_MIN, CORRIDOR_LIGHT_FACTOR_MAX)
    return max(64, min(255, int(round(base_light * factor))))


def random_room_light(base_light: int, rng: random.Random) -> int:
    factor = rng.uniform(ROOM_LIGHT_FACTOR_MIN, ROOM_LIGHT_FACTOR_MAX)
    return max(64, min(255, int(round(base_light * factor))))


def local_poly_bbox(poly: list[tuple[float, float]]) -> tuple[float, float, float, float]:
    xs = [p[0] for p in poly]
    ys = [p[1] for p in poly]
    return (min(xs), max(xs), min(ys), max(ys))


def boxes_intersect(a: tuple[float, float, float, float], b: tuple[float, float, float, float], pad: float = 0.0) -> bool:
    aminx, amaxx, aminy, amaxy = a
    bminx, bmaxx, bminy, bmaxy = b
    return not (
        (amaxx + pad) <= (bminx - pad)
        or (bmaxx + pad) <= (aminx - pad)
        or (amaxy + pad) <= (bminy - pad)
        or (bmaxy + pad) <= (aminy - pad)
    )


def signed_area_f(points: list[tuple[float, float]]) -> float:
    area2 = 0.0
    for idx in range(len(points)):
        x1, y1 = points[idx]
        x2, y2 = points[(idx + 1) % len(points)]
        area2 += (x1 * y2) - (x2 * y1)
    return area2 * 0.5


def polygon_area_abs(polygon: tuple[tuple[float, float], ...]) -> float:
    if len(polygon) < 3:
        return 0.0
    return abs(signed_area_f(list(polygon)))


def normalize_detail_polygon(points: list[tuple[float, float]]) -> list[tuple[float, float]]:
    cleaned: list[tuple[float, float]] = []
    for point in points:
        if cleaned and abs(point[0] - cleaned[-1][0]) < 1.0e-6 and abs(point[1] - cleaned[-1][1]) < 1.0e-6:
            continue
        cleaned.append(point)
    while len(cleaned) > 1 and abs(cleaned[0][0] - cleaned[-1][0]) < 1.0e-6 and abs(cleaned[0][1] - cleaned[-1][1]) < 1.0e-6:
        cleaned.pop()
    if len(cleaned) >= 3 and signed_area_f(cleaned) > 0.0:
        cleaned.reverse()
    return cleaned


def point_in_polygon(point: tuple[float, float], polygon: tuple[tuple[float, float], ...]) -> bool:
    x, y = point
    inside = False
    n = len(polygon)
    if n < 3:
        return False
    j = n - 1
    for i in range(n):
        xi, yi = polygon[i]
        xj, yj = polygon[j]
        intersects = ((yi > y) != (yj > y)) and (
            x < ((xj - xi) * (y - yi) / ((yj - yi) if abs(yj - yi) > 1.0e-9 else 1.0e-9) + xi)
        )
        if intersects:
            inside = not inside
        j = i
    return inside


def point_to_segment_distance_sq(
    point: tuple[float, float],
    a: tuple[float, float],
    b: tuple[float, float],
) -> float:
    px, py = point
    ax, ay = a
    bx, by = b
    vx = bx - ax
    vy = by - ay
    seg_len_sq = (vx * vx) + (vy * vy)
    if seg_len_sq <= 1.0e-9:
        dx = px - ax
        dy = py - ay
        return (dx * dx) + (dy * dy)
    t = ((px - ax) * vx + (py - ay) * vy) / seg_len_sq
    t = max(0.0, min(1.0, t))
    qx = ax + (vx * t)
    qy = ay + (vy * t)
    dx = px - qx
    dy = py - qy
    return (dx * dx) + (dy * dy)


def point_in_aabb(
    point: tuple[float, float],
    min_x: float,
    max_x: float,
    min_y: float,
    max_y: float,
) -> bool:
    px, py = point
    return (min_x <= px <= max_x) and (min_y <= py <= max_y)


def segment_to_segment_distance_sq(
    a1: tuple[float, float],
    a2: tuple[float, float],
    b1: tuple[float, float],
    b2: tuple[float, float],
) -> float:
    if segments_intersect(a1, a2, b1, b2):
        return 0.0
    return min(
        point_to_segment_distance_sq(a1, b1, b2),
        point_to_segment_distance_sq(a2, b1, b2),
        point_to_segment_distance_sq(b1, a1, a2),
        point_to_segment_distance_sq(b2, a1, a2),
    )


def segment_to_aabb_distance_sq(
    a: tuple[float, float],
    b: tuple[float, float],
    min_x: float,
    max_x: float,
    min_y: float,
    max_y: float,
) -> float:
    if point_in_aabb(a, min_x, max_x, min_y, max_y) or point_in_aabb(b, min_x, max_x, min_y, max_y):
        return 0.0
    edges = (
        ((min_x, min_y), (max_x, min_y)),
        ((max_x, min_y), (max_x, max_y)),
        ((max_x, max_y), (min_x, max_y)),
        ((min_x, max_y), (min_x, min_y)),
    )
    return min(segment_to_segment_distance_sq(a, b, e0, e1) for e0, e1 in edges)


def segments_intersect(
    a1: tuple[float, float],
    a2: tuple[float, float],
    b1: tuple[float, float],
    b2: tuple[float, float],
) -> bool:
    eps = 1.0e-9

    def orient(p: tuple[float, float], q: tuple[float, float], r: tuple[float, float]) -> float:
        return ((q[0] - p[0]) * (r[1] - p[1])) - ((q[1] - p[1]) * (r[0] - p[0]))

    def on_segment(p: tuple[float, float], q: tuple[float, float], r: tuple[float, float]) -> bool:
        return (
            min(p[0], q[0]) - eps <= r[0] <= max(p[0], q[0]) + eps
            and min(p[1], q[1]) - eps <= r[1] <= max(p[1], q[1]) + eps
        )

    o1 = orient(a1, a2, b1)
    o2 = orient(a1, a2, b2)
    o3 = orient(b1, b2, a1)
    o4 = orient(b1, b2, a2)
    if (o1 * o2 < -eps) and (o3 * o4 < -eps):
        return True
    if abs(o1) <= eps and on_segment(a1, a2, b1):
        return True
    if abs(o2) <= eps and on_segment(a1, a2, b2):
        return True
    if abs(o3) <= eps and on_segment(b1, b2, a1):
        return True
    if abs(o4) <= eps and on_segment(b1, b2, a2):
        return True
    return False


def polygon_self_intersects(polygon: tuple[tuple[float, float], ...]) -> bool:
    n = len(polygon)
    if n < 4:
        return False
    for i in range(n):
        a1 = polygon[i]
        a2 = polygon[(i + 1) % n]
        for j in range(i + 1, n):
            # skip same/adjacent edges and first-last adjacency
            if j == i or (j + 1) % n == i or j == (i + 1) % n:
                continue
            b1 = polygon[j]
            b2 = polygon[(j + 1) % n]
            if a1 == b1 or a1 == b2 or a2 == b1 or a2 == b2:
                continue
            if segments_intersect(a1, a2, b1, b2):
                return True
    return False


def min_distance_to_polygon_edges_sq(
    point: tuple[float, float],
    polygon: tuple[tuple[float, float], ...],
) -> float:
    if len(polygon) < 2:
        return float("inf")
    best = float("inf")
    for idx in range(len(polygon)):
        a = polygon[idx]
        b = polygon[(idx + 1) % len(polygon)]
        d2 = point_to_segment_distance_sq(point, a, b)
        if d2 < best:
            best = d2
    return best


def segment_to_segment_distance_sq(
    a1: tuple[float, float],
    a2: tuple[float, float],
    b1: tuple[float, float],
    b2: tuple[float, float],
) -> float:
    if segments_intersect(a1, a2, b1, b2):
        return 0.0
    return min(
        point_to_segment_distance_sq(a1, b1, b2),
        point_to_segment_distance_sq(a2, b1, b2),
        point_to_segment_distance_sq(b1, a1, a2),
        point_to_segment_distance_sq(b2, a1, a2),
    )


def min_edge_distance_between_polygons_sq(
    poly_a: tuple[tuple[float, float], ...],
    poly_b: tuple[tuple[float, float], ...],
) -> float:
    if len(poly_a) < 2 or len(poly_b) < 2:
        return float("inf")
    best = float("inf")
    for i in range(len(poly_a)):
        a1 = poly_a[i]
        a2 = poly_a[(i + 1) % len(poly_a)]
        for j in range(len(poly_b)):
            b1 = poly_b[j]
            b2 = poly_b[(j + 1) % len(poly_b)]
            d2 = segment_to_segment_distance_sq(a1, a2, b1, b2)
            if d2 < best:
                best = d2
                if best <= 0.0:
                    return 0.0
    return best


def min_edge_distance_polygon_to_segments_sq(
    polygon: tuple[tuple[float, float], ...],
    segments: list[tuple[tuple[float, float], tuple[float, float]]],
) -> float:
    if len(polygon) < 2 or not segments:
        return float("inf")
    best = float("inf")
    for i in range(len(polygon)):
        a1 = polygon[i]
        a2 = polygon[(i + 1) % len(polygon)]
        for b1, b2 in segments:
            d2 = segment_to_segment_distance_sq(a1, a2, b1, b2)
            if d2 < best:
                best = d2
                if best <= 0.0:
                    return 0.0
    return best


def find_overlapping_conflicting_linedefs(
    map_data: MutableMap,
    max_report: int = 24,
) -> list[str]:
    """Detect conflicting collinear overlaps and interior intersections."""
    reports: list[str] = []
    n = len(map_data.linedefs)
    if n <= 1:
        return reports
    doorframe_textures = {DOOR_TRACK_TEXTURE, *DOORFRAME_TRIPLE_TEXTURES, DOORFRAME_BASE_TEXTURE}

    def sectors_for_line(line: LineDef) -> tuple[int, int]:
        right_sector = -1
        left_sector = -1
        if 0 <= line.right < len(map_data.sidedefs):
            right_sector = int(map_data.sidedefs[line.right].sector)
        if 0 <= line.left < len(map_data.sidedefs):
            left_sector = int(map_data.sidedefs[line.left].sector)
        return right_sector, left_sector

    def line_bbox(v1: Vertex, v2: Vertex) -> tuple[float, float, float, float]:
        return (
            float(min(v1.x, v2.x)),
            float(max(v1.x, v2.x)),
            float(min(v1.y, v2.y)),
            float(max(v1.y, v2.y)),
        )

    def is_doorframe_detail_line(line: Linedef) -> bool:
        for side_idx in (line.right, line.left):
            if side_idx < 0 or side_idx >= len(map_data.sidedefs):
                continue
            side = map_data.sidedefs[side_idx]
            if (
                side.texture_top in doorframe_textures
                or side.texture_middle in doorframe_textures
                or side.texture_bottom in doorframe_textures
            ):
                return True
        return False

    def collinear_overlap_len(
        a1: tuple[float, float],
        a2: tuple[float, float],
        b1: tuple[float, float],
        b2: tuple[float, float],
    ) -> float:
        eps = 1.0e-6
        ax = a2[0] - a1[0]
        ay = a2[1] - a1[1]
        seg_len = math.hypot(ax, ay)
        if seg_len <= eps:
            return 0.0
        c1 = abs((ax * (b1[1] - a1[1])) - (ay * (b1[0] - a1[0])))
        c2 = abs((ax * (b2[1] - a1[1])) - (ay * (b2[0] - a1[0])))
        if c1 > (eps * seg_len) or c2 > (eps * seg_len):
            return 0.0
        if abs(ax) >= abs(ay):
            a_min = min(a1[0], a2[0])
            a_max = max(a1[0], a2[0])
            b_min = min(b1[0], b2[0])
            b_max = max(b1[0], b2[0])
        else:
            a_min = min(a1[1], a2[1])
            a_max = max(a1[1], a2[1])
            b_min = min(b1[1], b2[1])
            b_max = max(b1[1], b2[1])
        return max(0.0, min(a_max, b_max) - max(a_min, b_min))

    def intersects_interior(
        a1: tuple[float, float],
        a2: tuple[float, float],
        b1: tuple[float, float],
        b2: tuple[float, float],
    ) -> bool:
        div = (b2[1] - b1[1]) * (a2[0] - a1[0]) - (b2[0] - b1[0]) * (a2[1] - a1[1])
        if abs(div) <= 1.0e-9:
            return False
        u_line = ((b2[0] - b1[0]) * (a1[1] - b1[1]) - (b2[1] - b1[1]) * (a1[0] - b1[0])) / div
        u_ray = ((a2[0] - a1[0]) * (a1[1] - b1[1]) - (a2[1] - a1[1]) * (a1[0] - b1[0])) / div
        return (0.0 < u_line < 1.0) and (0.0 < u_ray < 1.0)

    micro_conflict_len = 24.0
    line_geom: list[
        tuple[
            tuple[float, float],
            tuple[float, float],
            tuple[float, float, float, float],
            tuple[int, int],
            float,
        ]
    ] = []
    line_is_detail: list[bool] = []
    for line in map_data.linedefs:
        line_is_detail.append(is_doorframe_detail_line(line))
        if not (0 <= line.v1 < len(map_data.vertices) and 0 <= line.v2 < len(map_data.vertices)):
            line_geom.append(((0.0, 0.0), (0.0, 0.0), (0.0, 0.0, 0.0, 0.0), (-1, -1), 0.0))
            continue
        v1 = map_data.vertices[line.v1]
        v2 = map_data.vertices[line.v2]
        a = (float(v1.x), float(v1.y))
        b = (float(v2.x), float(v2.y))
        seg_len = math.hypot(b[0] - a[0], b[1] - a[1])
        line_geom.append((a, b, line_bbox(v1, v2), sectors_for_line(line), seg_len))

    for i in range(n):
        a1, a2, abox, asectors, alen = line_geom[i]
        if abox == (0.0, 0.0, 0.0, 0.0):
            continue
        for j in range(i + 1, n):
            b1, b2, bbox, bsectors, blen = line_geom[j]
            if bbox == (0.0, 0.0, 0.0, 0.0):
                continue
            if not boxes_intersect(abox, bbox):
                continue
            if asectors == bsectors:
                continue
            if -1 in asectors or -1 in bsectors:
                # One-sided decorative/helper lines often intersect parent
                # boundaries in harmless ways for UDMF output.
                continue
            if line_is_detail[i] or line_is_detail[j]:
                # Doorframe helper geometry may legitimately create tiny T-junction-like
                # detail intersections that are not gameplay blockers.
                continue
            if min(alen, blen) <= micro_conflict_len:
                # Ignore tiny detail-segment clashes from decorative/alcove helpers.
                continue
            overlap_len = collinear_overlap_len(a1, a2, b1, b2)
            if overlap_len > 1.0:
                reports.append(
                    f"linedefs {i} and {j} overlap (len={overlap_len:.2f}) "
                    f"with different sectors {asectors} vs {bsectors}"
                )
            elif intersects_interior(a1, a2, b1, b2):
                reports.append(
                    f"linedefs {i} and {j} intersect in interior "
                    f"with different sectors {asectors} vs {bsectors}"
                )
            else:
                continue
            if len(reports) >= max_report:
                return reports
    return reports


def find_disconnected_room_sectors(
    map_data: MutableMap,
    room_sector_lookup: dict[int, int],
) -> list[int]:
    room_sectors = sorted(
        {
            int(sec_idx)
            for sec_idx in room_sector_lookup.values()
            if 0 <= int(sec_idx) < len(map_data.sectors)
        }
    )
    if len(room_sectors) <= 1:
        return []

    # Build full sector adjacency from all two-sided linedefs. Room reachability
    # should be evaluated through corridor/transition sectors, not only direct
    # room-to-room borders.
    adjacency: dict[int, set[int]] = {}
    for line in map_data.linedefs:
        if line.right < 0 or line.left < 0:
            continue
        if line.right >= len(map_data.sidedefs) or line.left >= len(map_data.sidedefs):
            continue
        a = int(map_data.sidedefs[line.right].sector)
        b = int(map_data.sidedefs[line.left].sector)
        if a == b:
            continue
        if a < 0 or b < 0:
            continue
        if a >= len(map_data.sectors) or b >= len(map_data.sectors):
            continue
        adjacency.setdefault(a, set()).add(b)
        adjacency.setdefault(b, set()).add(a)

    # Prefer the starting room (room index 0) as root when present.
    start = int(room_sector_lookup.get(0, room_sectors[0]))
    if start < 0 or start >= len(map_data.sectors):
        start = room_sectors[0]
    visited: set[int] = {start}
    queue: deque[int] = deque([start])
    while queue:
        cur = queue.popleft()
        for nxt in adjacency.get(cur, set()):
            if nxt in visited:
                continue
            visited.add(nxt)
            queue.append(nxt)

    return [sec for sec in room_sectors if sec not in visited]


def encode_udmf_textmap(map_data: MutableMap) -> bytes:
    parts: list[str] = ['namespace = "Doom";\n\n']

    for vertex in map_data.vertices:
        parts.append("vertex\n{\n")
        parts.append(f"    x = {vertex.x};\n")
        parts.append(f"    y = {vertex.y};\n")
        parts.append("}\n\n")

    # Normalize linedef side references before emission and rebuild sidedefs
    # and sectors from final line usage. This prevents sparse side indices
    # from surviving after line cleanup.
    serialized_sidedefs: list[Sidedef] = list(map_data.sidedefs)
    serialized_lines_raw: list[tuple[int, int, int, int, Linedef]] = []
    fallback_sector_idx = 0 if map_data.sectors else -1

    def make_fallback_front_sidedef() -> int:
        if fallback_sector_idx < 0:
            return -1
        serialized_sidedefs.append(
            Sidedef(
                offset_x=0,
                offset_y=0,
                texture_top="-",
                texture_bottom="-",
                texture_middle="-",
                sector=fallback_sector_idx,
            )
        )
        return len(serialized_sidedefs) - 1

    for line in map_data.linedefs:
        v1 = int(line.v1)
        v2 = int(line.v2)
        side_front = int(line.right)
        side_back = int(line.left)

        # Recover from one-sided lines that were stored on the left side only.
        if side_front < 0 <= side_back:
            v1, v2 = v2, v1
            side_front, side_back = side_back, -1

        if side_front < 0 or side_front >= len(serialized_sidedefs):
            repaired_front = make_fallback_front_sidedef()
            if repaired_front < 0:
                # No sector exists to anchor a fallback side; skip invalid line.
                continue
            side_front = repaired_front
            side_back = -1

        if side_back < 0 or side_back >= len(serialized_sidedefs):
            side_back = -1

        serialized_lines_raw.append((v1, v2, side_front, side_back, line))

    used_side_indices = sorted(
        {
            idx
            for _v1, _v2, front, back, _line in serialized_lines_raw
            for idx in (front, back)
            if idx >= 0
        }
    )
    side_remap: dict[int, int] = {}
    compact_sides: list[Sidedef] = []
    def optional_int(value: int | None) -> int | None:
        return None if value is None else int(value)

    for old_idx in used_side_indices:
        if old_idx < 0 or old_idx >= len(serialized_sidedefs):
            continue
        side = serialized_sidedefs[old_idx]
        sec = int(side.sector)
        if sec < 0 or sec >= len(map_data.sectors):
            sec = fallback_sector_idx if fallback_sector_idx >= 0 else 0
        side_remap[old_idx] = len(compact_sides)
        compact_sides.append(
            Sidedef(
                offset_x=int(side.offset_x),
                offset_y=int(side.offset_y),
                texture_top=side.texture_top,
                texture_bottom=side.texture_bottom,
                texture_middle=side.texture_middle,
                sector=sec,
                offset_x_top=optional_int(side.offset_x_top),
                offset_x_bottom=optional_int(side.offset_x_bottom),
                offset_x_middle=optional_int(side.offset_x_middle),
                offset_y_top=optional_int(side.offset_y_top),
                offset_y_bottom=optional_int(side.offset_y_bottom),
                offset_y_middle=optional_int(side.offset_y_middle),
            )
        )

    serialized_lines: list[tuple[int, int, int, int, Linedef]] = []
    for v1, v2, side_front, side_back, line in serialized_lines_raw:
        front_new = side_remap.get(int(side_front), -1)
        if front_new < 0:
            raise ValueError(
                f"{map_data.name}: linedef references missing front sidedef before export "
                f"(v1={v1}, v2={v2}, old_front={side_front})"
            )
        back_new = side_remap.get(int(side_back), -1) if side_back >= 0 else -1
        serialized_lines.append((v1, v2, front_new, back_new, line))

    used_sector_indices = sorted(
        {
            int(side.sector)
            for side in compact_sides
            if 0 <= int(side.sector) < len(map_data.sectors)
        }
    )
    if not used_sector_indices and map_data.sectors:
        used_sector_indices = [0]
    if not used_sector_indices:
        raise ValueError(f"{map_data.name}: cannot export TEXTMAP without at least one valid sector.")

    sector_remap: dict[int, int] = {old: new for new, old in enumerate(used_sector_indices)}
    compact_sectors: list[Sector] = [
        Sector(
            floor_height=int(map_data.sectors[old].floor_height),
            ceiling_height=int(map_data.sectors[old].ceiling_height),
            floor_texture=map_data.sectors[old].floor_texture,
            ceiling_texture=map_data.sectors[old].ceiling_texture,
            light_level=int(map_data.sectors[old].light_level),
            special=int(map_data.sectors[old].special),
            tag=int(map_data.sectors[old].tag),
        )
        for old in used_sector_indices
    ]
    for idx, side in enumerate(compact_sides):
        old_sec = int(side.sector)
        new_sec = sector_remap.get(old_sec, 0)
        compact_sides[idx] = Sidedef(
            offset_x=int(side.offset_x),
            offset_y=int(side.offset_y),
            texture_top=side.texture_top,
            texture_bottom=side.texture_bottom,
            texture_middle=side.texture_middle,
            sector=int(new_sec),
            offset_x_top=optional_int(side.offset_x_top),
            offset_x_bottom=optional_int(side.offset_x_bottom),
            offset_x_middle=optional_int(side.offset_x_middle),
            offset_y_top=optional_int(side.offset_y_top),
            offset_y_bottom=optional_int(side.offset_y_bottom),
            offset_y_middle=optional_int(side.offset_y_middle),
        )

    def side_sector(side_idx: int) -> int | None:
        if side_idx < 0 or side_idx >= len(compact_sides):
            return None
        sec = int(compact_sides[side_idx].sector)
        if 0 <= sec < len(compact_sectors):
            return sec
        return None

    missing_front_lines: list[int] = []
    missing_front_sector_lines: list[int] = []
    for line_idx, (_v1, _v2, side_front, _side_back, _line) in enumerate(serialized_lines):
        if side_front < 0 or side_front >= len(compact_sides):
            missing_front_lines.append(line_idx)
            continue
        if side_sector(side_front) is None:
            missing_front_sector_lines.append(line_idx)
    if missing_front_lines or missing_front_sector_lines:
        sample_front = ",".join(str(v) for v in missing_front_lines[:8])
        sample_sector = ",".join(str(v) for v in missing_front_sector_lines[:8])
        raise ValueError(
            f"{map_data.name}: pre-export front-side/front-sector validation failed "
            f"(missing_front=[{sample_front}], missing_front_sector=[{sample_sector}])"
        )

    left_vertex_side_counts: dict[int, int] = {}
    side_entries: list[tuple[int, bool, int, int]] = []
    line_state: dict[int, tuple[int | None, int | None, int | None, int | None]] = {}
    for line_idx, (v1, v2, side_front, side_back, _line) in enumerate(serialized_lines):
        front_entry: int | None = len(side_entries)
        side_entries.append((line_idx, True, int(v1), int(v2)))
        back_entry: int | None = None
        if side_back >= 0:
            back_entry = len(side_entries)
            side_entries.append((line_idx, False, int(v2), int(v1)))
        line_state[line_idx] = (
            front_entry,
            back_entry,
            side_sector(side_front),
            side_sector(side_back) if side_back >= 0 else None,
        )

    for _line_idx, _is_front, left_vertex, _right_vertex in side_entries:
        if 0 <= left_vertex < len(map_data.vertices):
            left_vertex_side_counts[left_vertex] = left_vertex_side_counts.get(left_vertex, 0) + 1

    unconnected_right_edge_lines: list[int] = []
    seen_unconnected: set[int] = set()
    for line_idx, is_front, _left_vertex, right_vertex in side_entries:
        front_entry, back_entry, front_sector, back_sector = line_state[line_idx]
        if front_sector == back_sector:
            other_side_ok = back_entry is not None if is_front else front_entry is not None
            if not other_side_ok and line_idx not in seen_unconnected:
                seen_unconnected.add(line_idx)
                unconnected_right_edge_lines.append(line_idx)
            continue
        if not (0 <= right_vertex < len(map_data.vertices)):
            continue
        if left_vertex_side_counts.get(right_vertex, 0) == 0 and line_idx not in seen_unconnected:
            seen_unconnected.add(line_idx)
            unconnected_right_edge_lines.append(line_idx)
    if unconnected_right_edge_lines:
        sample = ",".join(str(v) for v in unconnected_right_edge_lines[:8])
        raise ValueError(
            f"{map_data.name}: pre-export unconnected right-edge validation failed "
            f"(lines=[{sample}])"
        )

    for sector in compact_sectors:
        parts.append("sector\n{\n")
        parts.append(f"    heightfloor = {sector.floor_height};\n")
        parts.append(f"    heightceiling = {sector.ceiling_height};\n")
        parts.append(f'    texturefloor = "{udmf_escape(sector.floor_texture)}";\n')
        parts.append(f'    textureceiling = "{udmf_escape(sector.ceiling_texture)}";\n')
        parts.append(f"    lightlevel = {sector.light_level};\n")
        parts.append(f"    special = {sector.special};\n")
        parts.append(f"    id = {sector.tag};\n")
        parts.append("}\n\n")

    for sidedef in compact_sides:
        parts.append("sidedef\n{\n")
        parts.append(f"    offsetx = {sidedef.offset_x};\n")
        parts.append(f"    offsety = {sidedef.offset_y};\n")
        parts.append(f'    texturetop = "{udmf_escape(sidedef.texture_top)}";\n')
        parts.append(f'    texturebottom = "{udmf_escape(sidedef.texture_bottom)}";\n')
        parts.append(f'    texturemiddle = "{udmf_escape(sidedef.texture_middle)}";\n')
        parts.append(f"    sector = {sidedef.sector};\n")
        parts.append("}\n\n")

    for v1, v2, side_front, side_back, line in serialized_lines:
        flags = line.flags
        parts.append("linedef\n{\n")
        parts.append(f"    v1 = {v1};\n")
        parts.append(f"    v2 = {v2};\n")
        parts.append(f"    sidefront = {side_front};\n")
        if side_back >= 0:
            parts.append(f"    sideback = {side_back};\n")
        # UDMF standard flag name is "blocking" (not a custom alias).
        parts.append(udmf_bool("blocking", bool(flags & 0x0001)))
        parts.append(udmf_bool("blockmonsters", bool(flags & 0x0002)))
        parts.append(udmf_bool("twosided", side_back >= 0))
        parts.append(udmf_bool("dontpegtop", bool(flags & 0x0008)))
        parts.append(udmf_bool("dontpegbottom", bool(flags & 0x0010)))
        parts.append(udmf_bool("secret", bool(flags & 0x0020)))
        parts.append(udmf_bool("blocksound", bool(flags & 0x0040)))
        parts.append(udmf_bool("dontdraw", bool(flags & 0x0080)))
        parts.append(udmf_bool("mapped", bool(flags & 0x0100)))
        parts.append(f"    special = {line.special};\n")
        if int(line.special) in PLAYER_USE_LINE_SPECIALS:
            # Explicit only for known "use" actions in this generator.
            parts.append("    playeruse = true;\n")
        parts.append(f"    arg0 = {line.arg0};\n")
        parts.append(f"    arg1 = {line.arg1};\n")
        parts.append(f"    arg2 = {line.arg2};\n")
        parts.append(f"    arg3 = {line.arg3};\n")
        parts.append(f"    arg4 = {line.arg4};\n")
        parts.append(f"    id = {line.tag};\n")
        parts.append("}\n\n")

    for thing in map_data.things:
        flags = thing.flags
        easy = bool(flags & THING_FLAG_EASY)
        medium = bool(flags & THING_FLAG_MEDIUM)
        hard = bool(flags & THING_FLAG_HARD)
        if not (easy or medium or hard):
            easy = medium = hard = True
        multi_only = bool(flags & THING_FLAG_MULTI_ONLY)

        parts.append("thing\n{\n")
        parts.append(f"    x = {thing.x};\n")
        parts.append(f"    y = {thing.y};\n")
        parts.append("    height = 0;\n")
        parts.append(f"    angle = {thing.angle % 360};\n")
        parts.append(f"    type = {thing.thing_type};\n")
        parts.append(udmf_bool("skill1", easy))
        parts.append(udmf_bool("skill2", easy))
        parts.append(udmf_bool("skill3", medium))
        parts.append(udmf_bool("skill4", hard))
        parts.append(udmf_bool("skill5", hard))
        parts.append(udmf_bool("single", not multi_only))
        parts.append(udmf_bool("coop", True))
        parts.append(udmf_bool("dm", True))
        parts.append(udmf_bool("ambush", bool(flags & THING_FLAG_AMBUSH)))
        parts.append("}\n\n")

    return "".join(parts).encode("utf-8")


def counts_for_report(
    layout: GeneratedLayout,
    map_data: MutableMap,
    theme: ThemeStyle,
) -> tuple[int, int, int, int, int, int, int]:
    room_cells = sum(1 for row in layout.terrain for value in row if value == ROOM)
    corridor_cells = sum(1 for row in layout.terrain for value in row if value == CORRIDOR)
    transition_cells = sum(1 for row in layout.terrain for value in row if value == TRANSITION)
    corridor_floor_levels = {
        sector.floor_height
        for sector in map_data.sectors
        if sector.floor_texture == theme.corridor_floor
    }
    return (
        room_cells,
        corridor_cells,
        transition_cells,
        len(map_data.things),
        len(map_data.linedefs),
        len(map_data.sectors),
        len(corridor_floor_levels),
    )


def align_sunken_sector_lighting_to_rooms(
    map_data: MutableMap,
    layout: PolyLayout,
    room_sector_lookup: dict[int, int],
) -> int:
    # Keep same-height ceilings visually continuous by forcing all sunken
    # room-local sectors to inherit the room's light level.
    if not map_data.sectors or not room_sector_lookup:
        return 0

    sector_vertices: dict[int, set[int]] = {}
    for line in map_data.linedefs:
        for side_idx in (line.right, line.left):
            if side_idx < 0 or side_idx >= len(map_data.sidedefs):
                continue
            sec_idx = map_data.sidedefs[side_idx].sector
            if sec_idx < 0 or sec_idx >= len(map_data.sectors):
                continue
            vset = sector_vertices.setdefault(sec_idx, set())
            if 0 <= line.v1 < len(map_data.vertices):
                vset.add(line.v1)
            if 0 <= line.v2 < len(map_data.vertices):
                vset.add(line.v2)

    room_polys: list[tuple[tuple[float, float], ...]] = [
        tuple((float(x), float(y)) for x, y in room.polygon)
        for room in layout.rooms
    ]
    changed = 0

    for room_idx, room_sector_idx in room_sector_lookup.items():
        if room_idx < 0 or room_idx >= len(room_polys):
            continue
        if room_sector_idx < 0 or room_sector_idx >= len(map_data.sectors):
            continue
        room_poly = room_polys[room_idx]
        if not room_poly:
            continue
        room_sector = map_data.sectors[room_sector_idx]
        room_floor = int(room_sector.floor_height)
        room_light = int(room_sector.light_level)

        for sec_idx, sec in enumerate(map_data.sectors):
            if sec_idx == room_sector_idx:
                continue
            if not (
                int(sec.floor_height) < room_floor
                or int(sec.special) == int(SUNKEN_POOL_DAMAGE_SPECIAL)
            ):
                continue
            vset = sector_vertices.get(sec_idx, set())
            if not vset:
                continue
            points = [(float(map_data.vertices[v].x), float(map_data.vertices[v].y)) for v in vset]
            cx = sum(p[0] for p in points) / float(len(points))
            cy = sum(p[1] for p in points) / float(len(points))
            inside = point_in_polygon((cx, cy), room_poly)
            if not inside:
                inside = any(point_in_polygon(p, room_poly) for p in points)
            if not inside:
                continue
            if int(sec.light_level) != room_light:
                sec.light_level = room_light
                changed += 1

    return changed


def align_door_side_wall_offsets(map_data: MutableMap) -> int:
    """Clockwise room/corridor wall alignment with door-jamb seam preference."""
    if not map_data.linedefs or not map_data.sidedefs or not map_data.vertices or not map_data.sectors:
        return 0

    def has_track(side: Sidedef) -> bool:
        return DOOR_TRACK_TEXTURE in {side.texture_top, side.texture_middle, side.texture_bottom}

    marker_textures = set(DOORFRAME_TRIPLE_TEXTURES)

    def has_marker(side: Sidedef) -> bool:
        return (
            side.texture_top in marker_textures
            or side.texture_middle in marker_textures
            or side.texture_bottom in marker_textures
        )

    def slot_textures(side: Sidedef) -> tuple[str, str, str]:
        return (str(side.texture_top), str(side.texture_middle), str(side.texture_bottom))

    def pick_shared_texture(prev_side: Sidedef, cur_side: Sidedef) -> str:
        prev_slots = slot_textures(prev_side)
        cur_slots = slot_textures(cur_side)
        # Prioritize the current wall slot order, but allow full top/mid/bottom
        # permutation matching against the previous wall segment.
        for tex in cur_slots:
            if tex != "-" and tex not in marker_textures and tex in prev_slots:
                return tex
        for tex in prev_slots:
            if tex != "-" and tex not in marker_textures and tex in cur_slots:
                return tex
        return ""

    door_specials = set(DOOM_DOOR_SPECIAL_BY_COLOR.values())
    door_specials.add(DOOM_NONKEY_DOOR_SPECIAL)

    door_slab_sectors: set[int] = set()
    door_jamb_vertices: set[int] = set()
    for line in map_data.linedefs:
        if 0 <= line.right < len(map_data.sidedefs):
            rs = map_data.sidedefs[line.right]
            if has_track(rs):
                if 0 <= line.v1 < len(map_data.vertices):
                    door_jamb_vertices.add(int(line.v1))
                if 0 <= line.v2 < len(map_data.vertices):
                    door_jamb_vertices.add(int(line.v2))
        if 0 <= line.left < len(map_data.sidedefs):
            ls = map_data.sidedefs[line.left]
            if has_track(ls):
                if 0 <= line.v1 < len(map_data.vertices):
                    door_jamb_vertices.add(int(line.v1))
                if 0 <= line.v2 < len(map_data.vertices):
                    door_jamb_vertices.add(int(line.v2))

        if int(line.special) not in door_specials:
            continue
        side_secs: list[int] = []
        for side_idx in (line.right, line.left):
            if 0 <= side_idx < len(map_data.sidedefs):
                sec_idx = int(map_data.sidedefs[side_idx].sector)
                if 0 <= sec_idx < len(map_data.sectors):
                    side_secs.append(sec_idx)
        if not side_secs:
            continue
        zero_headroom = [
            sec_idx
            for sec_idx in side_secs
            if int(map_data.sectors[sec_idx].ceiling_height) <= int(map_data.sectors[sec_idx].floor_height)
        ]
        if zero_headroom:
            door_slab_sectors.update(zero_headroom)
            continue
        best = min(
            side_secs,
            key=lambda sec_idx: int(map_data.sectors[sec_idx].ceiling_height) - int(map_data.sectors[sec_idx].floor_height),
        )
        door_slab_sectors.add(int(best))

    @dataclass(frozen=True)
    class SectorEdge:
        side_idx: int
        line_idx: int
        sector_idx: int
        v_start: int
        v_end: int
        length: int
        touches_jamb: bool

    edges_by_sector: dict[int, list[SectorEdge]] = {}
    for line_idx, line in enumerate(map_data.linedefs):
        if not (0 <= line.v1 < len(map_data.vertices) and 0 <= line.v2 < len(map_data.vertices)):
            continue
        if int(line.special) != 0:
            # Keep moving door slab trigger lines untouched.
            continue

        v1 = map_data.vertices[line.v1]
        v2 = map_data.vertices[line.v2]
        seg_len = int(round(math.hypot(float(v2.x - v1.x), float(v2.y - v1.y))))
        if seg_len <= 0:
            continue

        def append_edge(side_idx: int, v_start: int, v_end: int) -> None:
            if side_idx < 0 or side_idx >= len(map_data.sidedefs):
                return
            side = map_data.sidedefs[side_idx]
            sec_idx = int(side.sector)
            if sec_idx < 0 or sec_idx >= len(map_data.sectors):
                return
            if sec_idx in door_slab_sectors:
                return
            if has_track(side):
                return
            if side.texture_top == "-" and side.texture_middle == "-" and side.texture_bottom == "-":
                return
            touches_jamb = (v_start in door_jamb_vertices) or (v_end in door_jamb_vertices)
            edges_by_sector.setdefault(sec_idx, []).append(
                SectorEdge(
                    side_idx=int(side_idx),
                    line_idx=int(line_idx),
                    sector_idx=sec_idx,
                    v_start=int(v_start),
                    v_end=int(v_end),
                    length=seg_len,
                    touches_jamb=touches_jamb,
                )
            )

        append_edge(int(line.right), int(line.v1), int(line.v2))
        append_edge(int(line.left), int(line.v2), int(line.v1))

    changed = 0
    for sector_idx, edges in sorted(edges_by_sector.items(), key=lambda item: int(item[0])):
        if not edges:
            continue
        by_start: dict[int, list[int]] = {}
        for edge_idx, edge in enumerate(edges):
            by_start.setdefault(int(edge.v_start), []).append(edge_idx)

        unvisited = set(range(len(edges)))
        prefer_jamb_start = any(edge.touches_jamb for edge in edges)
        while unvisited:
            if prefer_jamb_start:
                start_idx = next(
                    (edge_idx for edge_idx in sorted(unvisited) if edges[edge_idx].touches_jamb),
                    min(unvisited),
                )
                prefer_jamb_start = False
            else:
                start_idx = min(unvisited)

            chain: list[int] = []
            cur = int(start_idx)
            while cur in unvisited:
                unvisited.remove(cur)
                chain.append(cur)
                end_v = int(edges[cur].v_end)
                next_candidates = [n for n in by_start.get(end_v, []) if n in unvisited]
                if not next_candidates:
                    break
                cur = min(
                    next_candidates,
                    key=lambda n: (
                        int(edges[n].line_idx),
                        int(edges[n].side_idx),
                        int(n),
                    ),
                )

            if len(chain) < 2:
                continue

            for idx in range(1, len(chain)):
                prev_edge = edges[chain[idx - 1]]
                cur_edge = edges[chain[idx]]
                prev_side = map_data.sidedefs[prev_edge.side_idx]
                cur_side = map_data.sidedefs[cur_edge.side_idx]
                if has_marker(cur_side):
                    # Keep lock marker strips exactly where authored.
                    continue
                shared_tex = pick_shared_texture(prev_side, cur_side)
                if not shared_tex:
                    continue
                tex_width = texture_width_for_alignment(shared_tex)
                desired_raw = int(prev_side.offset_x) + int(prev_edge.length)
                desired = int(desired_raw % tex_width)
                if int(cur_side.offset_x) != desired:
                    cur_side.offset_x = desired
                    changed += 1

    return changed


def enforce_inner_jamb_doortrack(map_data: MutableMap) -> int:
    """Final pass: keep DOORTRAK only on two jamb lines per door."""
    if not map_data.linedefs or not map_data.sidedefs or not map_data.vertices or not map_data.sectors:
        return 0

    door_specials = set(DOOM_DOOR_SPECIAL_BY_COLOR.values())
    door_specials.add(DOOM_NONKEY_DOOR_SPECIAL)

    # Derive door slab sectors from door-special lines; prefer zero-headroom side.
    door_slab_sectors: set[int] = set()
    for line in map_data.linedefs:
        if int(line.special) not in door_specials:
            continue
        side_secs: list[int] = []
        for side_idx in (line.right, line.left):
            if 0 <= side_idx < len(map_data.sidedefs):
                sec = int(map_data.sidedefs[side_idx].sector)
                if 0 <= sec < len(map_data.sectors):
                    side_secs.append(sec)
        if not side_secs:
            continue
        zero_headroom = [sec for sec in side_secs if int(map_data.sectors[sec].ceiling_height) <= int(map_data.sectors[sec].floor_height)]
        if zero_headroom:
            door_slab_sectors.update(zero_headroom)
            continue
        best = min(
            side_secs,
            key=lambda sec: int(map_data.sectors[sec].ceiling_height) - int(map_data.sectors[sec].floor_height),
        )
        door_slab_sectors.add(int(best))

    if not door_slab_sectors:
        return 0

    face_len_sq = int((DOOR_NATIVE_WIDTH * 0.60) ** 2)
    target_lines: set[int] = set()
    context_sectors: set[int] = set(door_slab_sectors)

    for slab_sec in sorted(door_slab_sectors):
        face_entries: list[tuple[int, str, float, float, float]] = []
        side_entries: list[tuple[int, str, float, float, float, bool]] = []

        for idx, line in enumerate(map_data.linedefs):
            right_sec = map_data.sidedefs[line.right].sector if 0 <= line.right < len(map_data.sidedefs) else -1
            left_sec = map_data.sidedefs[line.left].sector if 0 <= line.left < len(map_data.sidedefs) else -1
            if not ((right_sec == slab_sec) ^ (left_sec == slab_sec)):
                continue

            other_sec = int(left_sec if right_sec == slab_sec else right_sec)
            if other_sec >= 0:
                context_sectors.add(other_sec)

            if not (0 <= line.v1 < len(map_data.vertices) and 0 <= line.v2 < len(map_data.vertices)):
                continue
            v1 = map_data.vertices[line.v1]
            v2 = map_data.vertices[line.v2]
            dx = float(v2.x - v1.x)
            dy = float(v2.y - v1.y)
            axis = "h" if abs(dx) >= abs(dy) else "v"
            seg_len = math.hypot(dx, dy)
            depth_mid = ((float(v1.x) + float(v2.x)) * 0.5) if axis == "h" else ((float(v1.y) + float(v2.y)) * 0.5)
            ortho_mid = ((float(v1.y) + float(v2.y)) * 0.5) if axis == "h" else ((float(v1.x) + float(v2.x)) * 0.5)
            if (dx * dx) + (dy * dy) >= float(face_len_sq):
                face_entries.append((idx, axis, depth_mid, ortho_mid, seg_len))
            else:
                one_sided = line.left < 0 or line.right < 0
                side_entries.append((idx, axis, depth_mid, ortho_mid, seg_len, one_sided))

        if not face_entries or not side_entries:
            continue

        face_axis = max(face_entries, key=lambda item: item[4])[1]
        side_axis = "v" if face_axis == "h" else "h"
        face_depth = sum(item[2] for item in face_entries) / float(len(face_entries))
        face_ortho = sum(item[3] for item in face_entries) / float(len(face_entries))

        # Prefer one-sided short lines on the slab perimeter (the true jamb strips).
        one_sided_candidates = [entry for entry in side_entries if entry[1] == side_axis and entry[5]]
        if len(one_sided_candidates) >= 2:
            neg = [entry for entry in one_sided_candidates if entry[3] <= face_ortho]
            pos = [entry for entry in one_sided_candidates if entry[3] >= face_ortho]
            if neg and pos:
                left_idx = max(neg, key=lambda item: item[3])[0]
                right_idx = min(pos, key=lambda item: item[3])[0]
            else:
                ordered = sorted(one_sided_candidates, key=lambda item: item[3])
                left_idx = ordered[0][0]
                right_idx = ordered[-1][0]
            target_lines.add(int(left_idx))
            target_lines.add(int(right_idx))
            continue

        candidates = [entry for entry in side_entries if entry[1] == side_axis]
        if not candidates:
            continue

        neg = [entry for entry in candidates if entry[3] < face_ortho]
        pos = [entry for entry in candidates if entry[3] >= face_ortho]

        def pick_middle(group: list[tuple[int, str, float, float, float, bool]]) -> int | None:
            if not group:
                return None
            return min(group, key=lambda item: abs(item[2] - face_depth))[0]

        left_idx = pick_middle(neg)
        right_idx = pick_middle(pos)
        if left_idx is not None:
            target_lines.add(int(left_idx))
        if right_idx is not None:
            target_lines.add(int(right_idx))

    changed = 0
    for idx, line in enumerate(map_data.linedefs):
        right_sec = map_data.sidedefs[line.right].sector if 0 <= line.right < len(map_data.sidedefs) else -1
        left_sec = map_data.sidedefs[line.left].sector if 0 <= line.left < len(map_data.sidedefs) else -1
        touches_context = (right_sec in context_sectors) or (left_sec in context_sectors)
        if not touches_context:
            continue

        if idx in target_lines:
            for side_idx in (line.right, line.left):
                if side_idx < 0 or side_idx >= len(map_data.sidedefs):
                    continue
                side = map_data.sidedefs[side_idx]
                if side.texture_top != "-" or side.texture_middle != DOOR_TRACK_TEXTURE or side.texture_bottom != "-":
                    side.texture_top = "-"
                    side.texture_middle = DOOR_TRACK_TEXTURE
                    side.texture_bottom = "-"
                    side.offset_y = 0
                    changed += 1
            line.flags &= ~0x0008
            line.flags |= 0x0010
            continue

        # Non-target lines in door context must not carry DOORTRAK.
        if line.left < 0 or line.right < 0:
            continue
        removed_any = False
        for side_idx in (line.right, line.left):
            if side_idx < 0 or side_idx >= len(map_data.sidedefs):
                continue
            side = map_data.sidedefs[side_idx]
            if DOOR_TRACK_TEXTURE in {side.texture_top, side.texture_middle, side.texture_bottom}:
                side.texture_top = "-"
                side.texture_middle = "-"
                side.texture_bottom = "-"
                side.offset_y = 0
                changed += 1
                removed_any = True
        if removed_any:
            line.flags &= ~0x0008
            line.flags &= ~0x0010
    return changed


def make_map_geometry(
    spec: EpisodeMapSpec,
    theme: ThemeStyle,
    rng: random.Random,
) -> tuple[
    PolyLayout,
    MutableMap,
    int,
    dict[int, list[tuple[tuple[float, float], ...]]],
    dict[int, list[tuple[tuple[float, float], ...]]],
    dict[int, list[tuple[tuple[float, float], ...]]],
    dict[int, list[tuple[float, float]]],
    MapPopulationTargets,
    dict[int, int],
]:
    # *** PASS 1: Plan Room/Corridor Topology + Validate Base Geometry ***
    last_layout_error: Exception | None = None
    layout: PolyLayout | None = None
    map_data: MutableMap | None = None
    door_lines_by_sector: dict[int, list[int]] | None = None
    door_sector_lookup: dict[int, tuple[int, int]] | None = None
    room_sector_lookup: dict[int, int] | None = None
    for layout_attempt in range(1, 33):
        log_event(f"LAYOUT_ATTEMPT map={spec.output_map} attempt={layout_attempt}/32")
        try:
            layout = generate_poly_layout(spec, theme, rng)
            (
                map_data_candidate,
                door_lines_candidate,
                door_sector_lookup_candidate,
                room_sector_lookup_candidate,
            ) = poly_layout_to_map(
                layout,
                spec.output_map,
                theme.door_texture,
            )
            overlap_conflicts = find_overlapping_conflicting_linedefs(map_data_candidate, max_report=8)
            if overlap_conflicts:
                raise ValueError(
                    "CORRIDOR_BBOX_CONFLICT "
                    f"map={spec.output_map} overlap_conflict={overlap_conflicts[0]}"
                )
            disconnected_room_sectors = find_disconnected_room_sectors(
                map_data_candidate,
                room_sector_lookup_candidate,
            )
            if disconnected_room_sectors:
                sample = ",".join(str(v) for v in disconnected_room_sectors[:8])
                raise ValueError(
                    "CORRIDOR_BBOX_CONFLICT "
                    f"map={spec.output_map} disconnected_room_sectors={sample}"
                )
            map_data = map_data_candidate
            door_lines_by_sector = door_lines_candidate
            door_sector_lookup = door_sector_lookup_candidate
            room_sector_lookup = room_sector_lookup_candidate
            log_event(f"LAYOUT_ATTEMPT_SUCCESS map={spec.output_map} attempt={layout_attempt}/32")
            break
        except ValueError as exc:
            if "CORRIDOR_BBOX_CONFLICT" not in str(exc):
                raise
            last_layout_error = exc
            log_event(
                f"LAYOUT_RETRY map={spec.output_map} attempt={layout_attempt}/32 "
                f"reason={exc}"
            )
            continue
    if layout is None or map_data is None or door_lines_by_sector is None or door_sector_lookup is None or room_sector_lookup is None:
        if last_layout_error is not None:
            log_event(
                f"LAYOUT_RETRY_EXHAUSTED map={spec.output_map} attempts=32 "
                f"latest={last_layout_error}"
            )
            raise ValueError(
                f"{spec.output_map}: failed to build corridor-safe layout after 32 attempts; "
                f"latest={last_layout_error}"
            ) from last_layout_error
        log_event(f"LAYOUT_RETRY_EXHAUSTED map={spec.output_map} attempts=32 latest=unknown")
        raise ValueError(f"{spec.output_map}: failed to build layout for unknown reason.")
    # *** PASS 2: Base Map Geometry Is Ready ***
    targets = MapPopulationTargets(
        rooms=list(range(len(layout.rooms))),
        platforms=[],
        corridors=list(range(len(layout.corridors))),
    )
    blocked_local_polys_by_room: dict[int, list[tuple[tuple[float, float], ...]]] = {}
    sunken_local_polys_by_room: dict[int, list[tuple[tuple[float, float], ...]]] = {}
    room_detail_count = 0
    decor_jobs: list[tuple[tuple[tuple[float, float], ...], int]] = []
    platform_local_polys_by_room: dict[int, list[tuple[tuple[float, float], ...]]] = {}
    room_free_mask_local_points_by_room: dict[int, list[tuple[float, float]]] = {}

    # *** PASS 3: Configure Progression Gates ***
    locked_door_colors: dict[int, str] = {}
    for edge_idx, room_idx, color in layout.lock_sequence:
        sector_idx = door_sector_lookup.get((edge_idx, room_idx))
        if sector_idx is not None:
            locked_door_colors[sector_idx] = color
    assign_door_actions(
        map_data,
        door_lines_by_sector,
        theme.door_texture,
        locked_door_colors=locked_door_colors,
    )

    # *** PASS 4: Place Start And Exit Features ***
    start_x, start_y, start_angle = preferred_start_anchor_poly(
        layout,
        blocked_local_polys_by_room=blocked_local_polys_by_room,
        sunken_local_polys_by_room=sunken_local_polys_by_room,
    )
    assign_start_entry_door(
        map_data,
        start_x,
        start_y,
        start_angle,
        required_front_sector=room_sector_lookup.get(0),
    )

    pref_x: int | None = None
    pref_y: int | None = None
    required_exit_sector: int | None = None
    exit_room_idx = select_exit_room_index(layout)
    if 0 <= exit_room_idx < len(layout.rooms):
        pref_x = int(round(layout.rooms[exit_room_idx].center[0]))
        pref_y = int(round(layout.rooms[exit_room_idx].center[1]))
        required_exit_sector = room_sector_lookup.get(exit_room_idx)
    assign_exit_switch(
        map_data,
        theme,
        start_x,
        start_y,
        preferred_x=pref_x,
        preferred_y=pref_y,
        required_front_sector=required_exit_sector,
    )
    if DEBUG:
        debug_sector = room_sector_lookup.get(0)
        try:
            assign_exit_switch(
                map_data,
                theme,
                start_x,
                start_y,
                preferred_x=start_x,
                preferred_y=start_y,
                required_front_sector=debug_sector,
            )
        except ValueError:
            assign_exit_switch(
                map_data,
                theme,
                start_x,
                start_y,
                preferred_x=start_x,
                preferred_y=start_y,
                required_front_sector=None,
            )

    # *** PASS 5: Apply Room Wall Detailing ***
    protected_rooms = {0}
    exit_room_idx = select_exit_room_index(layout)
    if 0 <= exit_room_idx < len(layout.rooms):
        protected_rooms.add(exit_room_idx)
    add_room_wall_texture_columns(
        map_data,
        layout,
        room_sector_lookup,
        spec.theme,
        rng,
        protected_room_indices=protected_rooms,
    )

    # *** PASS 6: Build Internal Room Sectors ***
    room_detail_count = 0
    blocked_local_polys_by_room.clear()
    sunken_local_polys_by_room.clear()
    decor_jobs.clear()
    platform_local_polys_by_room.clear()
    room_free_mask_local_points_by_room.clear()
    pool_state: dict[str, int] = {"placed_puddle_count": 0}
    skip_internal_details = DEBUG_SAFE_MAP03 and spec.output_map.upper() == "MAP03"
    if not skip_internal_details:
        for room_idx in range(len(layout.rooms)):
            (
                room_detail_count_part,
                blocked_part,
                sunken_part,
                decor_part,
                platform_part,
                free_mask_part,
            ) = add_room_internal_sectors(
                map_data,
                layout,
                room_sector_lookup,
                theme,
                spec.theme,
                rng,
                room_idx=room_idx,
                pool_state=pool_state,
            )
            room_detail_count += room_detail_count_part
            blocked_local_polys_by_room.update(blocked_part)
            sunken_local_polys_by_room.update(sunken_part)
            decor_jobs.extend(decor_part)
            platform_local_polys_by_room.update(platform_part)
            room_free_mask_local_points_by_room.update(free_mask_part)
    sunken_light_fixes = align_sunken_sector_lighting_to_rooms(
        map_data,
        layout,
        room_sector_lookup,
    )
    if sunken_light_fixes:
        log_trace(
            f"ROOM_LIGHT_ALIGN map={spec.output_map} adjusted_sunken_sectors={sunken_light_fixes}"
        )
    targets.platforms = list(decor_jobs)
    return (
        layout,
        map_data,
        room_detail_count,
        blocked_local_polys_by_room,
        sunken_local_polys_by_room,
        platform_local_polys_by_room,
        room_free_mask_local_points_by_room,
        targets,
        room_sector_lookup,
    )


def make_map(
    spec: EpisodeMapSpec,
    theme: ThemeStyle,
    rng: random.Random,
    monster_rng: random.Random | None = None,
) -> tuple[PolyLayout, MutableMap, int, dict[int, int]]:
    last_geom_error: Exception | None = None
    for map_attempt in range(1, 17):
        log_event(f"MAP_GEOM_ATTEMPT map={spec.output_map} attempt={map_attempt}/16")
        try:
            (
                layout,
                map_data,
                room_detail_count,
                blocked_local_polys_by_room,
                sunken_local_polys_by_room,
                platform_local_polys_by_room,
                room_free_mask_local_points_by_room,
                targets,
                room_sector_lookup,
            ) = make_map_geometry(spec, theme, rng)

            overlap_conflicts = find_overlapping_conflicting_linedefs(map_data, max_report=8)
            if overlap_conflicts:
                raise ValueError(
                    "CORRIDOR_BBOX_CONFLICT "
                    f"map={spec.output_map} final_overlap={overlap_conflicts[0]}"
                )

            add_map_objects(
                map_data,
                layout,
                spec,
                rng,
                monster_rng=monster_rng,
                population_targets=targets,
                blocked_local_polys_by_room=blocked_local_polys_by_room,
                sunken_local_polys_by_room=sunken_local_polys_by_room,
                platform_local_polys_by_room=platform_local_polys_by_room,
                room_free_mask_local_points_by_room=room_free_mask_local_points_by_room,
            )
            targets.rooms.clear()
            targets.platforms.clear()
            targets.corridors.clear()
            log_event(f"MAP_GEOM_ATTEMPT_SUCCESS map={spec.output_map} attempt={map_attempt}/16")
            return layout, map_data, room_detail_count, room_sector_lookup
        except ValueError as exc:
            if "CORRIDOR_BBOX_CONFLICT" not in str(exc):
                raise
            last_geom_error = exc
            log_event(
                f"MAP_GEOM_RETRY map={spec.output_map} attempt={map_attempt}/16 reason={exc}"
            )
            continue

    if last_geom_error is not None:
        log_event(
            f"MAP_GEOM_RETRY_EXHAUSTED map={spec.output_map} attempts=16 "
            f"latest={last_geom_error}"
        )
        raise ValueError(
            f"{spec.output_map}: failed to build conflict-free map geometry after 16 attempts; "
            f"latest={last_geom_error}"
        ) from last_geom_error
    log_event(f"MAP_GEOM_RETRY_EXHAUSTED map={spec.output_map} attempts=16 latest=unknown")
    raise ValueError(f"{spec.output_map}: failed to build map geometry for unknown reason.")


def verbose_geom_debug_enabled(map_name: str) -> bool:
    return False


def blue_key_room_index(layout: PolyLayout) -> int:
    for room_idx, color in layout.key_sequence:
        if color == "blue":
            return int(room_idx)
    return -1


def diagnostic_focus_room_index(map_data: MutableMap, layout: PolyLayout) -> int:
    map_name = map_data.name.strip().upper()
    # Current investigation target from field report:
    # MAP02 ROOM8.
    if map_name == "MAP02" and len(layout.rooms) > 8:
        return 8
    return blue_key_room_index(layout)


def dump_verbose_blue_room_geometry(
    map_data: MutableMap,
    layout: PolyLayout,
    room_sector_lookup: dict[int, int],
) -> None:
    map_name = map_data.name.strip().upper()
    if not verbose_geom_debug_enabled(map_name):
        return

    blue_room_idx = diagnostic_focus_room_index(map_data, layout)
    log_diag(
        f"[MAPDBG] map={map_name} key_sequence={layout.key_sequence} "
        f"lock_sequence={layout.lock_sequence} focus_room={blue_room_idx}"
    )
    if blue_room_idx < 0 or blue_room_idx >= len(layout.rooms):
        log_diag(f"[MAPDBG] map={map_name} focus_room missing or out of bounds")
        return

    room_poly = tuple(layout.rooms[blue_room_idx].polygon)
    room_sector = room_sector_lookup.get(blue_room_idx, -1)
    room_floor = map_data.sectors[room_sector].floor_height if 0 <= room_sector < len(map_data.sectors) else 0
    room_ceil = map_data.sectors[room_sector].ceiling_height if 0 <= room_sector < len(map_data.sectors) else 0
    log_diag(
        f"[MAPDBG] map={map_name} focus_room={blue_room_idx} room_sector={room_sector} "
        f"room_floor={room_floor} room_ceil={room_ceil} room_poly_vertices={len(room_poly)}"
    )
    for idx, point in enumerate(room_poly):
        log_diag(f"[MAPDBG] map={map_name} focus_room_poly_v idx={idx} x={point[0]:.3f} y={point[1]:.3f}")

    if room_sector < 0 or room_sector >= len(map_data.sectors):
        log_diag(f"[MAPDBG] map={map_name} invalid room_sector for focus room: {room_sector}")
        return

    # Collect room-local sectors by geometric containment so sunken sectors are
    # logged even if topology is unusual.
    sector_line_indices_all: dict[int, list[int]] = {}
    sector_vertices_all: dict[int, set[int]] = {}
    for line_idx, line in enumerate(map_data.linedefs):
        for side_idx in (line.right, line.left):
            if side_idx < 0 or side_idx >= len(map_data.sidedefs):
                continue
            sec_idx = map_data.sidedefs[side_idx].sector
            if sec_idx < 0 or sec_idx >= len(map_data.sectors):
                continue
            sector_line_indices_all.setdefault(sec_idx, []).append(line_idx)
            if 0 <= line.v1 < len(map_data.vertices):
                sector_vertices_all.setdefault(sec_idx, set()).add(line.v1)
            if 0 <= line.v2 < len(map_data.vertices):
                sector_vertices_all.setdefault(sec_idx, set()).add(line.v2)

    room_local_sectors: list[int] = []
    for sec_idx, vset in sector_vertices_all.items():
        if sec_idx == room_sector or not vset:
            continue
        points = [(float(map_data.vertices[v].x), float(map_data.vertices[v].y)) for v in sorted(vset)]
        cx = sum(p[0] for p in points) / float(len(points))
        cy = sum(p[1] for p in points) / float(len(points))
        inside = point_in_polygon((cx, cy), room_poly)
        if not inside:
            inside = any(point_in_polygon(p, room_poly) for p in points)
        if inside:
            room_local_sectors.append(sec_idx)

    room_local_sectors_sorted = sorted(set(room_local_sectors))
    sunken_local_sectors: list[int] = []
    for sec_idx in room_local_sectors_sorted:
        sec = map_data.sectors[sec_idx]
        is_sunken = (sec.floor_height < room_floor) or (sec.special == SUNKEN_POOL_DAMAGE_SPECIAL)
        if is_sunken:
            sunken_local_sectors.append(sec_idx)
        vset = sector_vertices_all.get(sec_idx, set())
        if vset:
            xs = [float(map_data.vertices[v].x) for v in sorted(vset)]
            ys = [float(map_data.vertices[v].y) for v in sorted(vset)]
            min_x = min(xs)
            max_x = max(xs)
            min_y = min(ys)
            max_y = max(ys)
            w = max_x - min_x
            h = max_y - min_y
            log_diag(
                f"[MAPDBG] map={map_name} ROOM_LOCAL_SECTOR room={blue_room_idx} sector={sec_idx} "
                f"floor={sec.floor_height} ceil={sec.ceiling_height} special={sec.special} "
                f"sunken={is_sunken} bbox=({min_x:.1f},{min_y:.1f})-({max_x:.1f},{max_y:.1f}) "
                f"size=({w:.1f},{h:.1f}) size_cells=({w / 64.0:.2f},{h / 64.0:.2f}) "
                f"lines={len(sector_line_indices_all.get(sec_idx, []))} verts={len(vset)}"
            )
        else:
            log_diag(
                f"[MAPDBG] map={map_name} ROOM_LOCAL_SECTOR room={blue_room_idx} sector={sec_idx} "
                f"floor={sec.floor_height} ceil={sec.ceiling_height} special={sec.special} "
                f"sunken={is_sunken} has_no_vertices"
            )
    log_diag(
        f"[MAPDBG] map={map_name} ROOM_LOCAL_SUMMARY room={blue_room_idx} "
        f"local_sectors={room_local_sectors_sorted} sunken_local_sectors={sorted(sunken_local_sectors)}"
    )

    touching_lines: list[int] = []
    touching_sectors: set[int] = {room_sector}
    for line_idx, line in enumerate(map_data.linedefs):
        right_sector = (
            map_data.sidedefs[line.right].sector
            if 0 <= line.right < len(map_data.sidedefs)
            else -1
        )
        left_sector = (
            map_data.sidedefs[line.left].sector
            if 0 <= line.left < len(map_data.sidedefs)
            else -1
        )
        if room_sector not in {right_sector, left_sector}:
            continue
        touching_lines.append(line_idx)
        if right_sector >= 0:
            touching_sectors.add(right_sector)
        if left_sector >= 0:
            touching_sectors.add(left_sector)

    log_diag(
        f"[MAPDBG] map={map_name} focus_room={blue_room_idx} touching_lines={len(touching_lines)} "
        f"touching_sectors={sorted(touching_sectors)}"
    )

    # Explicit wall-focused diagnostics for this room so perimeter geometry
    # is easy to inspect independently of internal/portal sectors.
    wall_lines: list[int] = []
    portal_lines: list[int] = []
    wall_vertices: set[int] = set()
    portal_target_sectors: set[int] = set()
    for line_idx in sorted(touching_lines):
        line = map_data.linedefs[line_idx]
        right_sector = (
            map_data.sidedefs[line.right].sector
            if 0 <= line.right < len(map_data.sidedefs)
            else -1
        )
        left_sector = (
            map_data.sidedefs[line.left].sector
            if 0 <= line.left < len(map_data.sidedefs)
            else -1
        )
        room_on_right = right_sector == room_sector
        room_on_left = left_sector == room_sector
        if (room_on_right and left_sector < 0) or (room_on_left and right_sector < 0):
            wall_lines.append(line_idx)
            if 0 <= line.v1 < len(map_data.vertices):
                wall_vertices.add(line.v1)
            if 0 <= line.v2 < len(map_data.vertices):
                wall_vertices.add(line.v2)
        else:
            portal_lines.append(line_idx)
            if room_on_right and left_sector >= 0:
                portal_target_sectors.add(left_sector)
            if room_on_left and right_sector >= 0:
                portal_target_sectors.add(right_sector)

    log_diag(
        f"[MAPDBG] map={map_name} ROOM_WALL_SUMMARY room={blue_room_idx} room_sector={room_sector} "
        f"wall_lines={len(wall_lines)} wall_vertices={len(wall_vertices)} "
        f"portal_lines={len(portal_lines)} portal_target_sectors={sorted(portal_target_sectors)}"
    )

    wall_degree: dict[int, int] = {}
    tiny_wall_count = 0
    for line_idx in wall_lines:
        line = map_data.linedefs[line_idx]
        if not (0 <= line.v1 < len(map_data.vertices) and 0 <= line.v2 < len(map_data.vertices)):
            log_diag(
                f"[MAPDBG] map={map_name} ROOM_WALL_LINE line={line_idx} invalid_vertex_ref "
                f"v1={line.v1} v2={line.v2}"
            )
            continue
        v1 = map_data.vertices[line.v1]
        v2 = map_data.vertices[line.v2]
        line_len = math.sqrt(float(line_length_sq(map_data, line_idx)))
        wall_degree[line.v1] = wall_degree.get(line.v1, 0) + 1
        wall_degree[line.v2] = wall_degree.get(line.v2, 0) + 1
        if line_len < 4.0:
            tiny_wall_count += 1
            log_diag(
                f"[MAPDBG] map={map_name} ROOM_WALL_TINY line={line_idx} len={line_len:.2f} "
                f"v1={line.v1}({v1.x},{v1.y}) v2={line.v2}({v2.x},{v2.y})"
            )
        log_diag(
            f"[MAPDBG] map={map_name} ROOM_WALL_LINE line={line_idx} "
            f"v1={line.v1}({v1.x},{v1.y}) v2={line.v2}({v2.x},{v2.y}) len={line_len:.2f} "
            f"flags=0x{line.flags:04x} special={line.special} right_side={line.right} left_side={line.left}"
        )
        if 0 <= line.right < len(map_data.sidedefs):
            rs = map_data.sidedefs[line.right]
            rs_sector = rs.sector
            log_diag(
                f"[MAPDBG] map={map_name} ROOM_WALL_LINE line={line_idx} right_sector={rs_sector} "
                f"right_tex top={rs.texture_top} mid={rs.texture_middle} bot={rs.texture_bottom}"
            )
        if 0 <= line.left < len(map_data.sidedefs):
            ls = map_data.sidedefs[line.left]
            ls_sector = ls.sector
            log_diag(
                f"[MAPDBG] map={map_name} ROOM_WALL_LINE line={line_idx} left_sector={ls_sector} "
                f"left_tex top={ls.texture_top} mid={ls.texture_middle} bot={ls.texture_bottom}"
            )

    odd_wall_vertices = [v for v, d in wall_degree.items() if d != 2]
    if tiny_wall_count > 0:
        log_diag(
            f"[MAPDBG] map={map_name} ROOM_WALL_HEALTH tiny_wall_segments={tiny_wall_count}"
        )
    if odd_wall_vertices:
        sample = ",".join(str(v) for v in odd_wall_vertices[:10])
        log_diag(
            f"[MAPDBG] map={map_name} ROOM_WALL_HEALTH non_loop_vertex_degree_count={len(odd_wall_vertices)} "
            f"sample={sample}"
        )

    for sector_idx in sorted(touching_sectors):
        if sector_idx < 0 or sector_idx >= len(map_data.sectors):
            continue
        sec = map_data.sectors[sector_idx]
        sector_line_indices: list[int] = []
        sector_vertices: set[int] = set()
        for line_idx, line in enumerate(map_data.linedefs):
            right_sector = (
                map_data.sidedefs[line.right].sector
                if 0 <= line.right < len(map_data.sidedefs)
                else -1
            )
            left_sector = (
                map_data.sidedefs[line.left].sector
                if 0 <= line.left < len(map_data.sidedefs)
                else -1
            )
            if sector_idx not in {right_sector, left_sector}:
                continue
            sector_line_indices.append(line_idx)
            if 0 <= line.v1 < len(map_data.vertices):
                sector_vertices.add(line.v1)
            if 0 <= line.v2 < len(map_data.vertices):
                sector_vertices.add(line.v2)
        if sector_vertices:
            xs = [float(map_data.vertices[v].x) for v in sorted(sector_vertices)]
            ys = [float(map_data.vertices[v].y) for v in sorted(sector_vertices)]
            min_x = min(xs)
            max_x = max(xs)
            min_y = min(ys)
            max_y = max(ys)
            w = max_x - min_x
            h = max_y - min_y
            log_diag(
                f"[MAPDBG] map={map_name} sector={sector_idx} floor={sec.floor_height} ceil={sec.ceiling_height} "
                f"special={sec.special} lines={len(sector_line_indices)} verts={len(sector_vertices)} "
                f"bbox=({min_x:.1f},{min_y:.1f})-({max_x:.1f},{max_y:.1f}) size=({w:.1f},{h:.1f}) "
                f"size_cells=({w / 64.0:.2f},{h / 64.0:.2f})"
            )
            if 120.0 <= w <= 136.0 and 120.0 <= h <= 136.0:
                log_diag(
                    f"[MAPDBG] map={map_name} sector={sector_idx} POSSIBLE_2x2_INTERNAL size=({w:.1f},{h:.1f})"
                )
        else:
            log_diag(
                f"[MAPDBG] map={map_name} sector={sector_idx} floor={sec.floor_height} "
                f"ceil={sec.ceiling_height} has_no_vertices"
            )
        for line_idx in sorted(sector_line_indices):
            line = map_data.linedefs[line_idx]
            if not (0 <= line.v1 < len(map_data.vertices) and 0 <= line.v2 < len(map_data.vertices)):
                log_diag(
                    f"[MAPDBG] map={map_name} sector={sector_idx} line={line_idx} invalid_vertex_ref "
                    f"v1={line.v1} v2={line.v2}"
                )
                continue
            v1 = map_data.vertices[line.v1]
            v2 = map_data.vertices[line.v2]
            right_sector = (
                map_data.sidedefs[line.right].sector
                if 0 <= line.right < len(map_data.sidedefs)
                else -1
            )
            left_sector = (
                map_data.sidedefs[line.left].sector
                if 0 <= line.left < len(map_data.sidedefs)
                else -1
            )
            line_len = math.sqrt(float(line_length_sq(map_data, line_idx)))
            log_diag(
                f"[MAPDBG] map={map_name} sector={sector_idx} line={line_idx} "
                f"v1={line.v1}({v1.x},{v1.y}) v2={line.v2}({v2.x},{v2.y}) len={line_len:.2f} "
                f"flags=0x{line.flags:04x} special={line.special} right_sector={right_sector} left_sector={left_sector}"
            )
            if 0 <= line.right < len(map_data.sidedefs):
                rs = map_data.sidedefs[line.right]
                log_diag(
                    f"[MAPDBG] map={map_name} sector={sector_idx} line={line_idx} right_tex "
                    f"top={rs.texture_top} mid={rs.texture_middle} bot={rs.texture_bottom} "
                    f"off=({rs.offset_x},{rs.offset_y})"
                )
            if 0 <= line.left < len(map_data.sidedefs):
                ls = map_data.sidedefs[line.left]
                log_diag(
                    f"[MAPDBG] map={map_name} sector={sector_idx} line={line_idx} left_tex "
                    f"top={ls.texture_top} mid={ls.texture_middle} bot={ls.texture_bottom} "
                    f"off=({ls.offset_x},{ls.offset_y})"
                )

    for line_idx in touching_lines:
        line = map_data.linedefs[line_idx]
        if not (0 <= line.v1 < len(map_data.vertices) and 0 <= line.v2 < len(map_data.vertices)):
            log_diag(
                f"[MAPDBG] map={map_name} line={line_idx} invalid_vertex_ref v1={line.v1} v2={line.v2}"
            )
            continue
        v1 = map_data.vertices[line.v1]
        v2 = map_data.vertices[line.v2]
        right_sector = (
            map_data.sidedefs[line.right].sector
            if 0 <= line.right < len(map_data.sidedefs)
            else -1
        )
        left_sector = (
            map_data.sidedefs[line.left].sector
            if 0 <= line.left < len(map_data.sidedefs)
            else -1
        )
        log_diag(
            f"[MAPDBG] map={map_name} line={line_idx} v1={line.v1}({v1.x},{v1.y}) "
            f"v2={line.v2}({v2.x},{v2.y}) len={math.sqrt(float(line_length_sq(map_data, line_idx))):.2f} "
            f"flags=0x{line.flags:04x} special={line.special} right_side={line.right} left_side={line.left} "
            f"right_sector={right_sector} left_sector={left_sector}"
        )
        if 0 <= line.right < len(map_data.sidedefs):
            rs = map_data.sidedefs[line.right]
            log_diag(
                f"[MAPDBG] map={map_name} line={line_idx} right_tex top={rs.texture_top} "
                f"mid={rs.texture_middle} bot={rs.texture_bottom} off=({rs.offset_x},{rs.offset_y})"
            )
        if 0 <= line.left < len(map_data.sidedefs):
            ls = map_data.sidedefs[line.left]
            log_diag(
                f"[MAPDBG] map={map_name} line={line_idx} left_tex top={ls.texture_top} "
                f"mid={ls.texture_middle} bot={ls.texture_bottom} off=({ls.offset_x},{ls.offset_y})"
            )


def dump_verbose_blue_key_things(
    map_data: MutableMap,
    layout: PolyLayout,
) -> None:
    map_name = map_data.name.strip().upper()
    if not verbose_geom_debug_enabled(map_name):
        return
    blue_room_idx = diagnostic_focus_room_index(map_data, layout)
    room_poly = tuple(layout.rooms[blue_room_idx].polygon) if 0 <= blue_room_idx < len(layout.rooms) else tuple()
    for thing_idx, thing in enumerate(map_data.things):
        if thing.thing_type != KEY_THING_BY_COLOR.get("blue"):
            continue
        in_blue_room = bool(room_poly) and point_in_polygon((float(thing.x), float(thing.y)), room_poly)
        log_diag(
            f"[MAPDBG] map={map_name} blue_key_thing idx={thing_idx} type={thing.thing_type} "
            f"pos=({thing.x},{thing.y}) angle={thing.angle} flags={thing.flags} in_blue_room={in_blue_room}"
        )


def matplotlib_enabled() -> bool:
    return ENABLE_PLOTS and (plt is not None)


def plot_thing_color(thing_type: int) -> str:
    """Color coding for map preview dots."""
    player_types = {1, 2, 3, 4}
    if thing_type in player_types:
        return "#111111"  # black

    monster_types = {
        t
        for weights in ROOM_MONSTER_WEIGHTS_BY_TIER.values()
        for t, _w in weights
    }
    monster_types.update(t for t, _w in CORRIDOR_MONSTER_WEIGHTS)
    if thing_type in monster_types:
        return "#cc2f2f"  # red

    decor_types = set()
    for values in DECOR_POOL_BY_THEME.values():
        decor_types.update(values)
    for values in SMALL_PLATFORM_DECOR_BY_THEME.values():
        decor_types.update(values)
    decor_types.add(2035)  # barrel
    if thing_type in decor_types:
        return "#1f6feb"  # blue

    pickup_types: set[int] = set()
    for tier_table in ROOM_PICKUP_TABLE_BY_TIER.values():
        pickup_types.update(thing_type for thing_type, _w in tier_table if thing_type > 0)
    for tier_table in CORRIDOR_PICKUP_TABLE_BY_TIER.values():
        pickup_types.update(thing_type for thing_type, _w in tier_table if thing_type > 0)
    pickup_types.update(KEY_THING_BY_COLOR.values())
    pickup_types.update(t for t, _w in TREASURE_ROOM_REWARD_WEIGHTS)
    pickup_types.update({2001, 2002, 2003, 2004, 2048, 2049, 2046, 2019, 82})
    if thing_type in pickup_types:
        return "#2da44e"  # green

    return "#111111"  # black


def export_map_png(
    map_data: MutableMap,
    output_dir: Path,
    *,
    exclude_line_ids: set[int] | None = None,
) -> Path | None:
    if not matplotlib_enabled():
        return None
    map_name = map_data.name.strip().upper() or "MAPXX"
    out_path = output_dir / f"{map_name}.png"
    fig, ax = plt.subplots(figsize=(10, 10), dpi=140)
    try:
        skip_lines = exclude_line_ids or set()
        for line_idx, line in enumerate(map_data.linedefs):
            if line_idx in skip_lines:
                continue
            if not (0 <= line.v1 < len(map_data.vertices) and 0 <= line.v2 < len(map_data.vertices)):
                continue
            v1 = map_data.vertices[line.v1]
            v2 = map_data.vertices[line.v2]
            ax.plot(
                (float(v1.x), float(v2.x)),
                (float(v1.y), float(v2.y)),
                color="#1e1e1e",
                linewidth=0.55,
                alpha=0.85,
            )
        if map_data.things:
            points_by_color: dict[str, list[tuple[float, float]]] = {}
            for thing in map_data.things:
                color = plot_thing_color(int(thing.thing_type))
                points_by_color.setdefault(color, []).append((float(thing.x), float(thing.y)))
            for color, points in points_by_color.items():
                tx = [p[0] for p in points]
                ty = [p[1] for p in points]
                ax.scatter(tx, ty, s=8, c=color, alpha=0.85)
        ax.set_title(f"{map_name} geometry")
        ax.set_aspect("equal", adjustable="box")
        ax.grid(True, linewidth=0.25, alpha=0.35)
        fig.tight_layout()
        fig.savefig(out_path, dpi=160)
    finally:
        plt.close(fig)
    log_diag(f"[PLOT] map={map_name} wrote_png={out_path}")
    return out_path


def collect_room_annotation_payload(
    map_data: MutableMap,
    layout: PolyLayout,
) -> list[dict[str, object]]:
    sector_vertices: dict[int, set[int]] = {}
    for line in map_data.linedefs:
        for side_idx in (line.right, line.left):
            if side_idx < 0 or side_idx >= len(map_data.sidedefs):
                continue
            sec_idx = map_data.sidedefs[side_idx].sector
            if sec_idx < 0 or sec_idx >= len(map_data.sectors):
                continue
            if 0 <= line.v1 < len(map_data.vertices):
                sector_vertices.setdefault(sec_idx, set()).add(line.v1)
            if 0 <= line.v2 < len(map_data.vertices):
                sector_vertices.setdefault(sec_idx, set()).add(line.v2)

    sector_centers: dict[int, tuple[float, float]] = {}
    for sec_idx, vids in sector_vertices.items():
        if len(vids) < 3:
            continue
        xs = [float(map_data.vertices[v].x) for v in vids]
        ys = [float(map_data.vertices[v].y) for v in vids]
        sector_centers[sec_idx] = (sum(xs) / float(len(xs)), sum(ys) / float(len(ys)))

    rooms: list[dict[str, object]] = []
    for room_idx, room in enumerate(layout.rooms):
        room_poly = tuple(room.polygon)
        if len(room_poly) < 3:
            continue
        line_ids: list[int] = []
        vertex_ids: set[int] = set()
        sector_ids: set[int] = set()
        for line_idx, line in enumerate(map_data.linedefs):
            if not (0 <= line.v1 < len(map_data.vertices) and 0 <= line.v2 < len(map_data.vertices)):
                continue
            v1 = map_data.vertices[line.v1]
            v2 = map_data.vertices[line.v2]
            mid = ((float(v1.x) + float(v2.x)) * 0.5, (float(v1.y) + float(v2.y)) * 0.5)
            touches_room = (
                point_in_polygon(mid, room_poly)
                or point_in_polygon((float(v1.x), float(v1.y)), room_poly)
                or point_in_polygon((float(v2.x), float(v2.y)), room_poly)
            )
            if not touches_room:
                continue
            line_ids.append(line_idx)
            vertex_ids.add(line.v1)
            vertex_ids.add(line.v2)
            for side_idx in (line.right, line.left):
                if 0 <= side_idx < len(map_data.sidedefs):
                    sec_idx = map_data.sidedefs[side_idx].sector
                    if 0 <= sec_idx < len(map_data.sectors):
                        sector_ids.add(sec_idx)

        cx = sum(float(p[0]) for p in room_poly) / float(len(room_poly))
        cy = sum(float(p[1]) for p in room_poly) / float(len(room_poly))
        rooms.append(
            {
                "room_id": int(room_idx),
                "center": (cx, cy),
                "line_ids": sorted(line_ids),
                "vertex_ids": sorted(vertex_ids),
                "sector_ids": sorted(sector_ids),
                "sector_centers": {int(sid): sector_centers.get(int(sid), (cx, cy)) for sid in sorted(sector_ids)},
                "poly": [(float(x), float(y)) for x, y in room_poly],
            }
        )
    return rooms


def collect_sector_centers(map_data: MutableMap) -> dict[int, tuple[float, float]]:
    sector_vertices: dict[int, set[int]] = {}
    for line in map_data.linedefs:
        for side_idx in (line.right, line.left):
            if side_idx < 0 or side_idx >= len(map_data.sidedefs):
                continue
            sec_idx = map_data.sidedefs[side_idx].sector
            if sec_idx < 0 or sec_idx >= len(map_data.sectors):
                continue
            if 0 <= line.v1 < len(map_data.vertices):
                sector_vertices.setdefault(sec_idx, set()).add(int(line.v1))
            if 0 <= line.v2 < len(map_data.vertices):
                sector_vertices.setdefault(sec_idx, set()).add(int(line.v2))

    centers: dict[int, tuple[float, float]] = {}
    for sec_idx, vids in sector_vertices.items():
        if not vids:
            continue
        xs = [float(map_data.vertices[v].x) for v in vids]
        ys = [float(map_data.vertices[v].y) for v in vids]
        centers[int(sec_idx)] = (sum(xs) / float(len(xs)), sum(ys) / float(len(ys)))
    return centers


def write_map_annotation_script(
    map_data: MutableMap,
    layout: PolyLayout,
    output_dir: Path,
    *,
    exclude_vertex_ids: set[int] | None = None,
    exclude_line_ids: set[int] | None = None,
    exclude_sector_ids: set[int] | None = None,
) -> Path:
    map_name = map_data.name.strip().upper() or "MAPXX"
    out_path = output_dir / f"{map_name}.py"
    skip_vertices = exclude_vertex_ids or set()
    skip_lines = exclude_line_ids or set()
    skip_sectors = exclude_sector_ids or set()

    vertices = [
        (int(v.x), int(v.y))
        for idx, v in enumerate(map_data.vertices)
        if idx not in skip_vertices
    ]
    lines = []
    for idx, line in enumerate(map_data.linedefs):
        if idx in skip_lines:
            continue
        if line.v1 in skip_vertices or line.v2 in skip_vertices:
            continue
        if not (0 <= line.v1 < len(map_data.vertices) and 0 <= line.v2 < len(map_data.vertices)):
            continue
        v1 = map_data.vertices[line.v1]
        v2 = map_data.vertices[line.v2]
        lines.append((idx, int(v1.x), int(v1.y), int(v2.x), int(v2.y)))
    sectors = [
        (idx, int(s.floor_height), int(s.ceiling_height), int(s.special))
        for idx, s in enumerate(map_data.sectors)
        if idx not in skip_sectors
    ]
    sector_centers = {
        sid: center
        for sid, center in collect_sector_centers(map_data).items()
        if sid not in skip_sectors
    }

    script = f"""#!/usr/bin/env python3
import matplotlib.pyplot as plt

MAP_NAME = {map_name!r}
VERTICES = {vertices!r}
LINES = {lines!r}
SECTORS = {sectors!r}
SECTOR_CENTERS = {sector_centers!r}

def main() -> None:
    fig, ax = plt.subplots(figsize=(16, 12), dpi=160)

    for lid, x1, y1, x2, y2 in LINES:
        ax.plot((x1, x2), (y1, y2), color="#1f1f1f", linewidth=0.55, alpha=0.8, zorder=1)
        mx = (float(x1) + float(x2)) * 0.5
        my = (float(y1) + float(y2)) * 0.5
        ax.text(mx, my, f"L{{lid}}", fontsize=5.8, color="#5a189a", zorder=6)

    for vid, (vx, vy) in enumerate(VERTICES):
        ax.scatter([vx], [vy], s=5, c="#2a9d8f", alpha=0.75, zorder=7)
        ax.text(float(vx) + 2.0, float(vy) + 2.0, f"V{{vid}}", fontsize=5.5, color="#2a9d8f", zorder=8)

    for sid, floor_h, ceil_h, special in SECTORS:
        sx, sy = SECTOR_CENTERS.get(sid, (0.0, 0.0))
        ax.text(
            float(sx),
            float(sy),
            f"S{{sid}}\\nF{{floor_h}} C{{ceil_h}} T{{special}}",
            fontsize=6.0,
            color="#bc6c25",
            ha="center",
            va="center",
            zorder=9,
        )

    ax.set_title(f"{{MAP_NAME}} full geometry labels (all L/V/S)")
    ax.set_aspect("equal", adjustable="box")
    ax.grid(True, linewidth=0.25, alpha=0.35)
    fig.tight_layout()
    plt.show()

if __name__ == "__main__":
    main()
"""
    out_path.write_text(script, encoding="utf-8")
    log_diag(f"[PLOT] map={map_name} wrote_annotation_script={out_path}")
    return out_path


def log_diag(message: str) -> None:
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3]
    try:
        with trace_log_path().open("a", encoding="utf-8") as fh:
            fh.write(f"{ts} {message}\n")
    except OSError:
        return


def log_linedef_texture_snapshot(
    map_data: MutableMap,
    map_name: str,
    start_idx: int,
    end_idx: int,
    label: str,
) -> None:
    lo = max(0, int(start_idx))
    hi = min(len(map_data.linedefs) - 1, int(end_idx))
    if hi < lo:
        return
    log_diag(f"[LINE_TEX][{label}] map={map_name} range={lo}-{hi}")
    for idx in range(lo, hi + 1):
        line = map_data.linedefs[idx]
        right_sector = -1
        left_sector = -1
        rtex_top = "-"
        rtex_mid = "-"
        rtex_bot = "-"
        ltex_top = "-"
        ltex_mid = "-"
        ltex_bot = "-"
        if 0 <= line.right < len(map_data.sidedefs):
            rs = map_data.sidedefs[line.right]
            right_sector = int(rs.sector)
            rtex_top = rs.texture_top
            rtex_mid = rs.texture_middle
            rtex_bot = rs.texture_bottom
        if 0 <= line.left < len(map_data.sidedefs):
            ls = map_data.sidedefs[line.left]
            left_sector = int(ls.sector)
            ltex_top = ls.texture_top
            ltex_mid = ls.texture_middle
            ltex_bot = ls.texture_bottom
        log_diag(
            "[LINE_TEX] "
            f"map={map_name} i={idx} v=({line.v1},{line.v2}) flags=0x{line.flags:04x} "
            f"spec={line.special} right={line.right}/S{right_sector} left={line.left}/S{left_sector} "
            f"R(t={rtex_top},m={rtex_mid},b={rtex_bot}) "
            f"L(t={ltex_top},m={ltex_mid},b={ltex_bot})"
        )


def diagnose_map_sector_integrity(map_data: MutableMap, map_name: str) -> int:
    def emit(level: str, msg: str) -> None:
        line = f"[SECTOR_DIAG][{level}] {map_name}: {msg}"
        log_diag(line)
        # Keep compatibility with --trace-log flow as well.
        log_trace(f"SECTOR_DIAG_{level} map={map_name} {msg}")

    issues = 0
    sidedef_use_by_sector: dict[int, int] = {}
    line_use_by_sector: dict[int, int] = {}
    vertex_use_by_sector: dict[int, set[int]] = {}
    sector_edges: dict[int, list[tuple[int, int, int]]] = {}
    sector_adj: dict[int, set[int]] = {}
    undirected_edge_seen: dict[tuple[int, int], int] = {}

    for sector_idx, sector in enumerate(map_data.sectors):
        if sector.ceiling_height < sector.floor_height:
            issues += 1
            emit(
                "ERROR",
                f"sector {sector_idx} has inverted heights (floor={sector.floor_height}, "
                f"ceiling={sector.ceiling_height})",
            )

    for side_idx, sidedef in enumerate(map_data.sidedefs):
        sector_idx = sidedef.sector
        if sector_idx < 0 or sector_idx >= len(map_data.sectors):
            issues += 1
            emit("ERROR", f"sidedef {side_idx} points to invalid sector {sector_idx}")
            continue
        sidedef_use_by_sector[sector_idx] = sidedef_use_by_sector.get(sector_idx, 0) + 1

    for line_idx, line in enumerate(map_data.linedefs):
        if line.v1 < 0 or line.v1 >= len(map_data.vertices) or line.v2 < 0 or line.v2 >= len(map_data.vertices):
            issues += 1
            emit(
                "ERROR",
                f"linedef {line_idx} has invalid vertex index (v1={line.v1}, v2={line.v2}, "
                f"vertices={len(map_data.vertices)})",
            )
            continue
        if line.v1 == line.v2:
            issues += 1
            emit("WARN", f"linedef {line_idx} is degenerate (v1 == v2 == {line.v1})")

        edge_key = (min(line.v1, line.v2), max(line.v1, line.v2))
        undirected_edge_seen[edge_key] = undirected_edge_seen.get(edge_key, 0) + 1
        if undirected_edge_seen[edge_key] > 2:
            issues += 1
            emit(
                "WARN",
                f"edge {edge_key[0]}-{edge_key[1]} is reused by {undirected_edge_seen[edge_key]} linedefs "
                f"(non-manifold/overlap risk)",
            )

        line_sector_refs: list[int] = []
        for side_label, side_idx in (("right", line.right), ("left", line.left)):
            if side_idx < 0:
                continue
            if side_idx >= len(map_data.sidedefs):
                issues += 1
                emit("ERROR", f"linedef {line_idx} has invalid {side_label} sidedef {side_idx}")
                continue
            sector_idx = map_data.sidedefs[side_idx].sector
            if sector_idx < 0 or sector_idx >= len(map_data.sectors):
                issues += 1
                emit(
                    "ERROR",
                    f"linedef {line_idx} {side_label} sidedef {side_idx} points to invalid sector {sector_idx}",
                )
                continue
            line_sector_refs.append(sector_idx)
            line_use_by_sector[sector_idx] = line_use_by_sector.get(sector_idx, 0) + 1
            vertex_use_by_sector.setdefault(sector_idx, set()).update((line.v1, line.v2))
            sector_edges.setdefault(sector_idx, []).append((line.v1, line.v2, line_idx))

        if line.left < 0 and line.right >= 0:
            rs = map_data.sidedefs[line.right]
            if rs.texture_middle == "-":
                issues += 1
                emit("WARN", f"one-sided linedef {line_idx} has blank middle texture (HOM risk)")
        if line.left >= 0 and line.right >= 0:
            left_sector = map_data.sidedefs[line.left].sector if line.left < len(map_data.sidedefs) else -1
            right_sector = map_data.sidedefs[line.right].sector if line.right < len(map_data.sidedefs) else -1
            if left_sector == right_sector and left_sector >= 0:
                issues += 1
                emit(
                    "WARN",
                    f"two-sided linedef {line_idx} references same sector on both sides ({left_sector})",
                )
            if left_sector >= 0 and right_sector >= 0 and left_sector != right_sector:
                sector_adj.setdefault(left_sector, set()).add(right_sector)
                sector_adj.setdefault(right_sector, set()).add(left_sector)

    for sector_idx in range(len(map_data.sectors)):
        side_count = sidedef_use_by_sector.get(sector_idx, 0)
        line_count = line_use_by_sector.get(sector_idx, 0)
        unique_vertices = len(vertex_use_by_sector.get(sector_idx, set()))
        if side_count == 0:
            issues += 1
            emit("WARN", f"sector {sector_idx} is unreferenced by sidedefs")
        if line_count > 0 and unique_vertices < 3:
            issues += 1
            emit(
                "WARN",
                f"sector {sector_idx} has too few unique vertices ({unique_vertices}) across attached linedefs",
            )

        # Sector boundary sanity: manifold loops should produce degree-2 vertices.
        edge_list = sector_edges.get(sector_idx, [])
        if edge_list:
            degree: dict[int, int] = {}
            for v1, v2, _ in edge_list:
                degree[v1] = degree.get(v1, 0) + 1
                degree[v2] = degree.get(v2, 0) + 1
            odd_or_non2 = [v for v, d in degree.items() if d != 2]
            if odd_or_non2:
                issues += 1
                sample = ",".join(str(v) for v in odd_or_non2[:6])
                emit(
                    "WARN",
                    f"sector {sector_idx} boundary has non-loop vertex degrees (count={len(odd_or_non2)} sample={sample})",
                )

    # Sector connectivity check over 2-sided adjacencies.
    referenced_sectors = [idx for idx in range(len(map_data.sectors)) if sidedef_use_by_sector.get(idx, 0) > 0]
    # Connectivity warning should target navigable cross-sector graph only.
    # Sealed one-sided detail sectors can be valid and should not count as
    # disconnected components.
    adjacency_referenced = [idx for idx in referenced_sectors if sector_adj.get(idx)]
    if adjacency_referenced:
        start = adjacency_referenced[0]
        visited: set[int] = set()
        q: deque[int] = deque([start])
        visited.add(start)
        while q:
            cur = q.popleft()
            for nxt in sector_adj.get(cur, set()):
                if nxt in visited:
                    continue
                visited.add(nxt)
                q.append(nxt)
        disconnected = [s for s in adjacency_referenced if s not in visited]
        if disconnected:
            sample = ",".join(str(v) for v in disconnected[:10])
            emit(
                "INFO",
                f"sector adjacency graph is disconnected (components>1, disconnected_count={len(disconnected)}, sample={sample})",
            )

    if issues == 0:
        emit(
            "OK",
            f"sectors={len(map_data.sectors)} sidedefs={len(map_data.sidedefs)} linedefs={len(map_data.linedefs)}",
        )
    else:
        emit("SUMMARY", f"issues={issues}")
    return issues


def sanitize_generated_map_geometry(map_data: MutableMap) -> dict[str, int]:
    """Best-effort cleanup pass for procedurally generated geometry."""
    dropped_invalid_lines = 0
    dropped_open_open_lines = 0
    converted_open_lines_to_onesided = 0
    dropped_lines_after_reindex = 0
    dropped_sidedefs = 0
    dropped_sectors = 0
    dropped_vertices = 0
    merged_degenerate_sliver_sectors = 0
    merged_nonclosed_sectors = 0
    cleared_unused_upper_textures = 0
    cleared_unused_lower_textures = 0

    original_lines = list(map_data.linedefs)
    original_sides = list(map_data.sidedefs)
    original_sectors = list(map_data.sectors)
    original_vertices = list(map_data.vertices)

    def is_action_line(line: Linedef) -> bool:
        return (
            int(line.special) != 0
            or int(line.tag) != 0
            or int(line.arg0) != 0
            or int(line.arg1) != 0
            or int(line.arg2) != 0
            or int(line.arg3) != 0
            or int(line.arg4) != 0
        )

    # Pass 1: normalize obviously invalid linedefs.
    normalized_lines: list[Linedef] = []
    for line in original_lines:
        v1 = int(line.v1)
        v2 = int(line.v2)
        right = int(line.right)
        left = int(line.left)
        if v1 < 0 or v2 < 0 or v1 >= len(original_vertices) or v2 >= len(original_vertices) or v1 == v2:
            dropped_invalid_lines += 1
            continue
        right_valid = 0 <= right < len(original_sides)
        left_valid = 0 <= left < len(original_sides)
        if not right_valid and left_valid:
            # Recover mirrored one-sided representation.
            v1, v2 = v2, v1
            right, left = left, -1
            right_valid, left_valid = True, False
        if not right_valid:
            dropped_invalid_lines += 1
            continue
        if not left_valid:
            left = -1
        if left == right and left >= 0:
            left = -1
        normalized_lines.append(
            Linedef(
                v1=v1,
                v2=v2,
                flags=int(line.flags),
                special=int(line.special),
                tag=int(line.tag),
                right=right,
                left=left,
                arg0=int(line.arg0),
                arg1=int(line.arg1),
                arg2=int(line.arg2),
                arg3=int(line.arg3),
                arg4=int(line.arg4),
            )
        )

    # Repair pass: merge zero-height one-sidedef sliver sectors into an
    # adjacent valid sector when possible. These slivers are generated by
    # tiny marker/cap remnants and trigger "sector not closed" diagnostics.
    sector_to_sides: dict[int, list[int]] = {}
    for side_idx, side in enumerate(original_sides):
        sec = int(side.sector)
        if 0 <= sec < len(original_sectors):
            sector_to_sides.setdefault(sec, []).append(side_idx)
    side_to_lines: dict[int, list[Linedef]] = {}
    for line in normalized_lines:
        if 0 <= line.right < len(original_sides):
            side_to_lines.setdefault(int(line.right), []).append(line)
        if 0 <= line.left < len(original_sides):
            side_to_lines.setdefault(int(line.left), []).append(line)
    for sec_idx, side_indices in sector_to_sides.items():
        if len(side_indices) != 1:
            continue
        sector = original_sectors[sec_idx]
        if int(sector.floor_height) != int(sector.ceiling_height):
            continue
        side_idx = side_indices[0]
        refs = side_to_lines.get(side_idx, [])
        neighbor_sector = -1
        for line in refs:
            other_side_idx = int(line.left) if int(line.right) == side_idx else int(line.right)
            if other_side_idx < 0 or other_side_idx >= len(original_sides):
                continue
            candidate = int(original_sides[other_side_idx].sector)
            if 0 <= candidate < len(original_sectors) and candidate != sec_idx:
                neighbor_sector = candidate
                break
        if neighbor_sector >= 0:
            original_sides[side_idx].sector = neighbor_sector
            merged_degenerate_sliver_sectors += 1

    # Pass 2: detect open sectors by vertex degree parity/coverage.
    sector_degree: dict[int, dict[int, int]] = {}
    for line in normalized_lines:
        for side_idx in (line.right, line.left):
            if side_idx < 0 or side_idx >= len(original_sides):
                continue
            sec = int(original_sides[side_idx].sector)
            if sec < 0 or sec >= len(original_sectors):
                continue
            deg = sector_degree.setdefault(sec, {})
            deg[line.v1] = deg.get(line.v1, 0) + 1
            deg[line.v2] = deg.get(line.v2, 0) + 1

    open_sectors: set[int] = set()
    lock_marker_textures = set(LOCK_FRAME_TEXTURE_BY_COLOR.values())
    lock_marker_textures.update(DOORFRAME_TRIPLE_TEXTURES)
    lock_marker_textures.add(DOOR_TRACK_TEXTURE)
    lock_marker_textures.add(DOORFRAME_BASE_TEXTURE)
    for sec_idx, deg in sector_degree.items():
        sector = original_sectors[sec_idx]
        # Preserve intentional "cap" helper sectors used for lock marker strips.
        if int(sector.floor_height) == int(sector.ceiling_height):
            continue
        if len(deg) < 3:
            open_sectors.add(sec_idx)
            continue
        bad = False
        for count in deg.values():
            if count < 2 or (count % 2) != 0:
                bad = True
                break
        if bad:
            open_sectors.add(sec_idx)

    # Pass 3: remove/repair linedefs touching open sectors.
    repaired_lines: list[Linedef] = []
    for line in normalized_lines:
        right_sec = -1
        left_sec = -1
        if 0 <= line.right < len(original_sides):
            right_sec = int(original_sides[line.right].sector)
        if 0 <= line.left < len(original_sides):
            left_sec = int(original_sides[line.left].sector)
        right_open = right_sec in open_sectors
        left_open = left_sec in open_sectors

        # Never auto-rewrite/drop gameplay action lines in best-effort cleanup.
        if is_action_line(line):
            repaired_lines.append(line)
            continue

        if right_open and left_open:
            dropped_open_open_lines += 1
            continue
        if right_open and line.left >= 0:
            # Keep surviving side as right/front.
            converted_open_lines_to_onesided += 1
            repaired_lines.append(
                Linedef(
                    v1=line.v2,
                    v2=line.v1,
                    flags=int(line.flags),
                    special=int(line.special),
                    tag=int(line.tag),
                    right=int(line.left),
                    left=-1,
                    arg0=int(line.arg0),
                    arg1=int(line.arg1),
                    arg2=int(line.arg2),
                    arg3=int(line.arg3),
                    arg4=int(line.arg4),
                )
            )
            continue
        if left_open:
            converted_open_lines_to_onesided += 1
            repaired_lines.append(
                Linedef(
                    v1=int(line.v1),
                    v2=int(line.v2),
                    flags=int(line.flags),
                    special=int(line.special),
                    tag=int(line.tag),
                    right=int(line.right),
                    left=-1,
                    arg0=int(line.arg0),
                    arg1=int(line.arg1),
                    arg2=int(line.arg2),
                    arg3=int(line.arg3),
                    arg4=int(line.arg4),
                )
            )
            continue
        repaired_lines.append(line)

    # Pass 4: compact sidedefs/sectors and keep one-sided wall textures valid.
    used_side_indices: set[int] = set()
    for line in repaired_lines:
        if line.right >= 0:
            used_side_indices.add(int(line.right))
        if line.left >= 0:
            used_side_indices.add(int(line.left))

    side_remap: dict[int, int] = {}
    compact_sides: list[Sidedef] = []
    for old_idx, side in enumerate(original_sides):
        if old_idx not in used_side_indices:
            continue
        sec = int(side.sector)
        if sec < 0 or sec >= len(original_sectors):
            dropped_sidedefs += 1
            continue
        side_remap[old_idx] = len(compact_sides)
        compact_sides.append(
            Sidedef(
                offset_x=int(side.offset_x),
                offset_y=int(side.offset_y),
                texture_top=side.texture_top,
                texture_bottom=side.texture_bottom,
                texture_middle=side.texture_middle,
                sector=sec,
                offset_x_top=side.offset_x_top,
                offset_x_bottom=side.offset_x_bottom,
                offset_x_middle=side.offset_x_middle,
                offset_y_top=side.offset_y_top,
                offset_y_bottom=side.offset_y_bottom,
                offset_y_middle=side.offset_y_middle,
            )
        )

    remapped_lines: list[Linedef] = []
    for line in repaired_lines:
        right = side_remap.get(int(line.right), -1)
        left = side_remap.get(int(line.left), -1) if line.left >= 0 else -1
        if right < 0:
            dropped_lines_after_reindex += 1
            continue
        remapped_lines.append(
            Linedef(
                v1=int(line.v1),
                v2=int(line.v2),
                flags=int(line.flags),
                special=int(line.special),
                tag=int(line.tag),
                right=right,
                left=left,
                arg0=int(line.arg0),
                arg1=int(line.arg1),
                arg2=int(line.arg2),
                arg3=int(line.arg3),
                arg4=int(line.arg4),
            )
        )

    # Second repair pass: merge non-loop (open) sectors into adjacent sectors.
    sector_degree_after_remap: dict[int, dict[int, int]] = {}
    for line in remapped_lines:
        for side_idx in (line.right, line.left):
            if side_idx < 0 or side_idx >= len(compact_sides):
                continue
            sec = int(compact_sides[side_idx].sector)
            if sec < 0 or sec >= len(original_sectors):
                continue
            deg = sector_degree_after_remap.setdefault(sec, {})
            deg[line.v1] = deg.get(line.v1, 0) + 1
            deg[line.v2] = deg.get(line.v2, 0) + 1

    open_nonloop_sectors: set[int] = set()
    for sec_idx, deg in sector_degree_after_remap.items():
        sector = original_sectors[sec_idx]
        if int(sector.floor_height) == int(sector.ceiling_height):
            continue
        if len(deg) < 3:
            open_nonloop_sectors.add(sec_idx)
            continue
        if any(count != 2 for count in deg.values()):
            open_nonloop_sectors.add(sec_idx)

    if open_nonloop_sectors:
        repaired_after_open: list[Linedef] = []
        for line in remapped_lines:
            right_sec = int(compact_sides[line.right].sector) if 0 <= line.right < len(compact_sides) else -1
            left_sec = int(compact_sides[line.left].sector) if 0 <= line.left < len(compact_sides) else -1
            right_open = right_sec in open_nonloop_sectors
            left_open = left_sec in open_nonloop_sectors

            # Keep gameplay action lines intact even if a surrounding sector is suspect.
            if is_action_line(line):
                repaired_after_open.append(line)
                continue

            if right_open and left_open:
                dropped_open_open_lines += 1
                continue
            if right_open:
                if line.left >= 0:
                    converted_open_lines_to_onesided += 1
                    repaired_after_open.append(
                        Linedef(
                            v1=int(line.v2),
                            v2=int(line.v1),
                            flags=int(line.flags),
                            special=int(line.special),
                            tag=int(line.tag),
                            right=int(line.left),
                            left=-1,
                            arg0=int(line.arg0),
                            arg1=int(line.arg1),
                            arg2=int(line.arg2),
                            arg3=int(line.arg3),
                            arg4=int(line.arg4),
                        )
                    )
                else:
                    dropped_open_open_lines += 1
                continue
            if left_open:
                converted_open_lines_to_onesided += 1
                repaired_after_open.append(
                    Linedef(
                        v1=int(line.v1),
                        v2=int(line.v2),
                        flags=int(line.flags),
                        special=int(line.special),
                        tag=int(line.tag),
                        right=int(line.right),
                        left=-1,
                        arg0=int(line.arg0),
                        arg1=int(line.arg1),
                        arg2=int(line.arg2),
                        arg3=int(line.arg3),
                        arg4=int(line.arg4),
                    )
                )
                continue
            repaired_after_open.append(line)
        remapped_lines = repaired_after_open

        side_to_lines_after: dict[int, list[Linedef]] = {}
        for line in remapped_lines:
            if 0 <= line.right < len(compact_sides):
                side_to_lines_after.setdefault(int(line.right), []).append(line)
            if 0 <= line.left < len(compact_sides):
                side_to_lines_after.setdefault(int(line.left), []).append(line)

        for side_idx, side in enumerate(compact_sides):
            sec_idx = int(side.sector)
            if sec_idx not in open_nonloop_sectors:
                continue
            neighbor_sec = -1
            for line in side_to_lines_after.get(side_idx, []):
                other_side_idx = int(line.left) if int(line.right) == side_idx else int(line.right)
                if other_side_idx < 0 or other_side_idx >= len(compact_sides):
                    continue
                candidate = int(compact_sides[other_side_idx].sector)
                if (
                    0 <= candidate < len(original_sectors)
                    and candidate != sec_idx
                    and candidate not in open_nonloop_sectors
                ):
                    neighbor_sec = candidate
                    break
            if neighbor_sec >= 0:
                side.sector = neighbor_sec
                merged_nonclosed_sectors += 1

    used_sector_indices = {side.sector for side in compact_sides if 0 <= side.sector < len(original_sectors)}
    sector_remap: dict[int, int] = {}
    compact_sectors: list[Sector] = []
    for old_idx, sector in enumerate(original_sectors):
        if old_idx not in used_sector_indices:
            continue
        sector_remap[old_idx] = len(compact_sectors)
        compact_sectors.append(
            Sector(
                floor_height=int(sector.floor_height),
                ceiling_height=int(sector.ceiling_height),
                floor_texture=sector.floor_texture,
                ceiling_texture=sector.ceiling_texture,
                light_level=int(sector.light_level),
                special=int(sector.special),
                tag=int(sector.tag),
            )
        )
    dropped_sectors = len(original_sectors) - len(compact_sectors)

    for side in compact_sides:
        side.sector = sector_remap.get(side.sector, 0 if compact_sectors else -1)

    for line in remapped_lines:
        if line.left < 0:
            side = compact_sides[line.right]
            if side.texture_middle == "-":
                if side.texture_bottom in lock_marker_textures:
                    side.texture_middle = side.texture_bottom
                elif side.texture_top in lock_marker_textures:
                    side.texture_middle = side.texture_top
                else:
                    side.texture_middle = (
                        side.texture_top
                        if side.texture_top != "-"
                        else (side.texture_bottom if side.texture_bottom != "-" else "STARTAN3")
                    )
            side.texture_top = "-"
            side.texture_bottom = "-"
        else:
            right_side = compact_sides[line.right]
            left_side = compact_sides[line.left]
            right_sec = int(right_side.sector)
            left_sec = int(left_side.sector)
            if (
                0 <= right_sec < len(compact_sectors)
                and 0 <= left_sec < len(compact_sectors)
                and right_sec != left_sec
            ):
                right_sector = compact_sectors[right_sec]
                left_sector = compact_sectors[left_sec]
                right_needs_upper = left_sector.ceiling_height < right_sector.ceiling_height
                left_needs_upper = right_sector.ceiling_height < left_sector.ceiling_height
                right_needs_lower = left_sector.floor_height > right_sector.floor_height
                left_needs_lower = right_sector.floor_height > left_sector.floor_height

                if is_action_line(line):
                    continue

                if right_side.texture_top != "-" and not right_needs_upper and right_side.texture_top not in lock_marker_textures:
                    right_side.texture_top = "-"
                    cleared_unused_upper_textures += 1
                if left_side.texture_top != "-" and not left_needs_upper and left_side.texture_top not in lock_marker_textures:
                    left_side.texture_top = "-"
                    cleared_unused_upper_textures += 1
                if right_side.texture_bottom != "-" and not right_needs_lower and right_side.texture_bottom not in lock_marker_textures:
                    right_side.texture_bottom = "-"
                    cleared_unused_lower_textures += 1
                if left_side.texture_bottom != "-" and not left_needs_lower and left_side.texture_bottom not in lock_marker_textures:
                    left_side.texture_bottom = "-"
                    cleared_unused_lower_textures += 1

    used_vertex_indices: set[int] = set()
    for line in remapped_lines:
        used_vertex_indices.add(int(line.v1))
        used_vertex_indices.add(int(line.v2))
    vertex_remap: dict[int, int] = {}
    compact_vertices: list[Vertex] = []
    for old_idx, vertex in enumerate(original_vertices):
        if old_idx not in used_vertex_indices:
            continue
        vertex_remap[old_idx] = len(compact_vertices)
        compact_vertices.append(Vertex(x=int(vertex.x), y=int(vertex.y)))
    dropped_vertices = len(original_vertices) - len(compact_vertices)

    final_lines: list[Linedef] = []
    for line in remapped_lines:
        if line.v1 not in vertex_remap or line.v2 not in vertex_remap:
            dropped_lines_after_reindex += 1
            continue
        final_lines.append(
            Linedef(
                v1=vertex_remap[line.v1],
                v2=vertex_remap[line.v2],
                flags=int(line.flags),
                special=int(line.special),
                tag=int(line.tag),
                right=int(line.right),
                left=int(line.left),
                arg0=int(line.arg0),
                arg1=int(line.arg1),
                arg2=int(line.arg2),
                arg3=int(line.arg3),
                arg4=int(line.arg4),
            )
        )

    dropped_sidedefs += len(original_sides) - len(compact_sides)
    map_data.vertices = compact_vertices
    map_data.sectors = compact_sectors
    map_data.sidedefs = compact_sides
    map_data.linedefs = final_lines

    return {
        "dropped_invalid_lines": dropped_invalid_lines,
        "dropped_open_open_lines": dropped_open_open_lines,
        "converted_open_lines_to_onesided": converted_open_lines_to_onesided,
        "dropped_lines_after_reindex": dropped_lines_after_reindex,
        "dropped_sidedefs": dropped_sidedefs,
        "dropped_sectors": dropped_sectors,
        "dropped_vertices": dropped_vertices,
        "merged_degenerate_sliver_sectors": merged_degenerate_sliver_sectors,
        "merged_nonclosed_sectors": merged_nonclosed_sectors,
        "cleared_unused_upper_textures": cleared_unused_upper_textures,
        "cleared_unused_lower_textures": cleared_unused_lower_textures,
    }


def build_pwad(output: Path, specs: list[EpisodeMapSpec], *, build_znodes: bool = True) -> BuildResult:
    log_trace(f"BUILD_START output={output} maps={len(specs)}")
    out_lumps: list[Lump] = []
    reports: list[str] = []
    out_lumps.append(Lump("MAPINFO", encode_mapinfo_level_names(specs)))
    out_lumps.append(Lump("ANIMDEFS", encode_animdefs()))
    plot_notice_emitted = False

    total_maps = len(specs)
    for map_idx, spec in enumerate(specs, start=1):
        map_t0 = time.perf_counter()
        set_trace_map_timer(spec.output_map)
        signature_exclude_line_ids: set[int] = set()
        signature_exclude_vertex_ids: set[int] = set()
        signature_exclude_sector_ids: set[int] = set()
        print(f"[{map_idx}/{total_maps}] Building {spec.output_map} ({spec.theme})...", flush=True)
        log_event(f"MAP_BEGIN map={spec.output_map} seed={spec.map_seed} theme={spec.theme}")
        theme = THEMES.get(spec.theme)
        if theme is None:
            raise ValueError(f"Unknown theme '{spec.theme}'.")
        chosen_seed = int(spec.map_seed)
        rng = random.Random(chosen_seed)
        monster_rng = random.Random(chosen_seed ^ 0x555555AA)
        layout, map_data, room_detail_count, room_sector_lookup = make_map(
            spec,
            theme,
            rng,
            monster_rng=monster_rng,
        )

        # Debug probe: append a tiny hidden square room at the very end of map
        # construction so the final linedefs are unrelated to gameplay geometry.
        if DEBUG_APPEND_DUMMY_LAST_LINE:
            room_size = 128
            base_x = 30000 - (map_idx * 256)
            base_y = -30000 + (map_idx * 256)
            hidden_sector = add_sector(
                map_data,
                floor_height=0,
                ceiling_height=128,
                floor_texture=theme.room_floor,
                ceiling_texture=theme.ceiling_flat,
                light_level=theme.room_light,
                special=0,
                tag=0,
            )
            v0 = len(map_data.vertices)
            map_data.vertices.append(Vertex(base_x, base_y))
            map_data.vertices.append(Vertex(base_x, base_y + room_size))
            map_data.vertices.append(Vertex(base_x + room_size, base_y + room_size))
            map_data.vertices.append(Vertex(base_x + room_size, base_y))
            line_ids: list[int] = []
            neighbor_sector = 0
            line_ids.append(
                add_boundary_line(
                    map_data,
                    v1_idx=v0 + 0,
                    v2_idx=v0 + 1,
                    right_sector=hidden_sector,
                    left_sector=neighbor_sector,
                    right_wall_texture=theme.room_wall_textures[0],
                    left_wall_texture=theme.room_wall_textures[1] if len(theme.room_wall_textures) > 1 else theme.room_wall_textures[0],
                )
            )
            line_ids.append(
                add_boundary_line(
                    map_data,
                    v1_idx=v0 + 1,
                    v2_idx=v0 + 2,
                    right_sector=hidden_sector,
                    left_sector=neighbor_sector,
                    right_wall_texture=theme.room_wall_textures[0],
                    left_wall_texture=theme.room_wall_textures[1] if len(theme.room_wall_textures) > 1 else theme.room_wall_textures[0],
                )
            )
            line_ids.append(
                add_boundary_line(
                    map_data,
                    v1_idx=v0 + 2,
                    v2_idx=v0 + 3,
                    right_sector=hidden_sector,
                    left_sector=neighbor_sector,
                    right_wall_texture=theme.room_wall_textures[0],
                    left_wall_texture=theme.room_wall_textures[1] if len(theme.room_wall_textures) > 1 else theme.room_wall_textures[0],
                )
            )
            line_ids.append(
                add_boundary_line(
                    map_data,
                    v1_idx=v0 + 3,
                    v2_idx=v0 + 0,
                    right_sector=hidden_sector,
                    left_sector=neighbor_sector,
                    right_wall_texture=theme.room_wall_textures[0],
                    left_wall_texture=theme.room_wall_textures[1] if len(theme.room_wall_textures) > 1 else theme.room_wall_textures[0],
                )
            )
            last_idx = len(map_data.linedefs) - 1
            log_diag(
                f"[LASTLINE_PROBE] map={spec.output_map} appended_hidden_room "
                f"sector={hidden_sector} vertices={v0},{v0+1},{v0+2},{v0+3} "
                f"lines={line_ids} last_line={last_idx}"
            )

        # Easy-to-remove probe block: append one isolated 1x1 signature room.
        # Keep this last so these linedefs get the highest indices.
        if DRAW_SIGNATURE:
            room_floor = 0
            room_ceil = 128
            room_light = theme.room_light
            wall_tex = theme.room_wall_textures[0]
            base_x = 24000 - (map_idx * 512)
            base_y = -24000 + (map_idx * 384)
            room_size = max(1, int(TILE))
            added_line_start = len(map_data.linedefs)
            v_start = len(map_data.vertices)
            corners = (
                (base_x, base_y),
                (base_x + room_size, base_y),
                (base_x + room_size, base_y + room_size),
                (base_x, base_y + room_size),
            )
            for px, py in corners:
                map_data.vertices.append(Vertex(int(px), int(py)))
            sig_sector = add_sector(
                map_data,
                floor_height=room_floor,
                ceiling_height=room_ceil,
                floor_texture=theme.room_floor,
                ceiling_texture=theme.ceiling_flat,
                light_level=room_light,
                special=0,
                tag=0,
            )
            line_ids = [
                add_boundary_line(
                    map_data,
                    v1_idx=v_start + 0,
                    v2_idx=v_start + 1,
                    right_sector=sig_sector,
                    left_sector=-1,
                    right_wall_texture=wall_tex,
                ),
                add_boundary_line(
                    map_data,
                    v1_idx=v_start + 1,
                    v2_idx=v_start + 2,
                    right_sector=sig_sector,
                    left_sector=-1,
                    right_wall_texture=wall_tex,
                ),
                add_boundary_line(
                    map_data,
                    v1_idx=v_start + 2,
                    v2_idx=v_start + 3,
                    right_sector=sig_sector,
                    left_sector=-1,
                    right_wall_texture=wall_tex,
                ),
                add_boundary_line(
                    map_data,
                    v1_idx=v_start + 3,
                    v2_idx=v_start + 0,
                    right_sector=sig_sector,
                    left_sector=-1,
                    right_wall_texture=wall_tex,
                ),
            ]
            signature_exclude_sector_ids.add(int(sig_sector))
            signature_exclude_vertex_ids.update({int(v_start + 0), int(v_start + 1), int(v_start + 2), int(v_start + 3)})
            signature_exclude_line_ids.update(int(line_id) for line_id in line_ids)
            added_line_end = len(map_data.linedefs) - 1
            log_diag(
                f"[LASTLINE_PROBE] map={spec.output_map} appended_signature_room_1x1 "
                f"sector={sig_sector} vertices={v_start},{v_start+1},{v_start+2},{v_start+3} "
                f"lines={line_ids} line_range={added_line_start}..{added_line_end}"
            )
        sanitize_stats = sanitize_generated_map_geometry(map_data)
        post_sanitize_light_fixes = align_sunken_sector_lighting_to_rooms(
            map_data,
            layout,
            room_sector_lookup,
        )
        if post_sanitize_light_fixes:
            sanitize_stats["post_sanitize_pool_light_fixes"] = post_sanitize_light_fixes
            log_trace(
                f"ROOM_LIGHT_ALIGN_POST_SANITIZE map={spec.output_map} "
                f"adjusted_sunken_sectors={post_sanitize_light_fixes}"
            )
        post_sanitize_jamb_track = enforce_inner_jamb_doortrack(map_data)
        if post_sanitize_jamb_track:
            sanitize_stats["post_sanitize_jamb_track"] = post_sanitize_jamb_track
            log_trace(
                f"DOOR_JAMB_TRACK_POST_SANITIZE map={spec.output_map} "
                f"adjusted_sidedefs={post_sanitize_jamb_track}"
            )
        post_sanitize_halign = align_door_side_wall_offsets(map_data)
        if post_sanitize_halign:
            sanitize_stats["post_sanitize_texture_halign"] = post_sanitize_halign
            log_trace(
                f"DOOR_SIDE_HALIGN_POST_SANITIZE map={spec.output_map} "
                f"adjusted_sidedefs={post_sanitize_halign}"
            )
        if VERBOSE_TRACE_LOG:
            log_linedef_texture_snapshot(
                map_data,
                spec.output_map,
                start_idx=0,
                end_idx=149,
                label="FIRST150",
            )
            log_linedef_texture_snapshot(
                map_data,
                spec.output_map,
                start_idx=132,
                end_idx=145,
                label="L132_145",
            )
            log_linedef_texture_snapshot(
                map_data,
                spec.output_map,
                start_idx=210,
                end_idx=245,
                label="L210_245",
            )
        sector_diag_issues = diagnose_map_sector_integrity(map_data, spec.output_map)
        textmap = encode_udmf_textmap(map_data)

        # Emit plot/debug artifacts from finalized map state (after sanitize/align).            
        try:
            annotation_script_path: Path | None = None
            if matplotlib_enabled():
                annotation_script_path = write_map_annotation_script(
                    map_data,
                    layout,
                    output.parent,
                    exclude_vertex_ids=signature_exclude_vertex_ids,
                    exclude_line_ids=signature_exclude_line_ids,
                    exclude_sector_ids=signature_exclude_sector_ids,
                )
            if annotation_script_path is not None:
                print(f"[PLOT] Wrote {annotation_script_path.name}", flush=True)
        except Exception as plot_exc:
            plot_line = f"[PLOT][WARN] map={spec.output_map} annotation_script_failed error={plot_exc!r}"
            print(plot_line, flush=True)
            log_diag(plot_line)
        if matplotlib_enabled():
            try:
                map_plot_path = export_map_png(
                    map_data,
                    output.parent,
                    exclude_line_ids=signature_exclude_line_ids,
                )
                if map_plot_path is not None:
                    print(f"[PLOT] Saved {map_plot_path.name}", flush=True)
            except Exception as plot_exc:
                plot_line = f"[PLOT][WARN] map={spec.output_map} plotting_failed error={plot_exc!r}"
                print(plot_line, flush=True)
                log_diag(plot_line)
        elif not plot_notice_emitted:
            plot_notice_emitted = True
            print("[PLOT] matplotlib not available; skipping PNG exports.", flush=True)
            log_diag("[PLOT] matplotlib not available; skipping PNG exports")

        out_lumps.append(Lump(spec.output_map, b""))
        out_lumps.append(Lump("TEXTMAP", textmap))
        out_lumps.append(Lump("ENDMAP", b""))

        rooms, corridor_sectors, things, lines, corridor_levels = counts_for_poly_report(layout, map_data, theme)
        reports.append(
            (
                f"{spec.output_map} | theme={spec.theme} | seed={chosen_seed} | "
                f"build_seconds={time.perf_counter() - map_t0:.3f} | "
                f"sector_diag_issues={sector_diag_issues} | sanitize={sanitize_stats} | rooms={rooms} | "
                f"corridor_sectors={corridor_sectors} | "
                f"room_detail_sectors={room_detail_count} | "
                f"things={things}, linedefs={lines}, sectors={len(map_data.sectors)}, "
                f"corridor_floor_levels={corridor_levels}"
            )
        )
        map_elapsed = time.perf_counter() - map_t0
        print(f"[TIME] {spec.output_map} build_seconds={map_elapsed:.3f}", flush=True)
        log_event(
            f"MAP_DONE map={spec.output_map} theme={spec.theme} seed={chosen_seed} "
            f"build_seconds={map_elapsed:.3f} "
            f"sector_diag_issues={sector_diag_issues} "
            f"sanitize={sanitize_stats} "
            f"rooms={rooms} corridor_sectors={corridor_sectors} room_detail_sectors={room_detail_count} "
            f"things={things} linedefs={lines} sectors={len(map_data.sectors)} "
            f"corridor_floor_levels={corridor_levels}"
        )
        clear_trace_map_timer()

    output_wad = Wad("PWAD", out_lumps)
    write_wad(output, output_wad)
    if build_znodes:
        znodes_ok, znodes_msg = try_build_znodes_with_zdbsp(output)
        if znodes_ok:
            print("[NODES] Embedded ZNODES via zdbsp.", flush=True)
            log_event(f"NODES_OK output={output} detail={znodes_msg}")
        else:
            warn = f"[NODES][WARN] could not build ZNODES ({znodes_msg})"
            print(warn, flush=True)
            log_event(f"NODES_WARN output={output} detail={znodes_msg}")
    else:
        log_event(f"NODES_SKIP output={output} reason=disabled")
    log_trace(f"BUILD_DONE output={output}")
    return BuildResult(
        output_path=output,
        map_reports=reports,
        compatibility_profile=(
            "UDMF (Doom namespace) procedural corridor maps with MAPxx/TEXTMAP/ENDMAP lumps, "
            "intended for GZDoom + Brutal Doom."
        ),
    )


def resolve_path(path_arg: str, base_dir: Path) -> Path:
    raw = Path(path_arg)
    return raw if raw.is_absolute() else (base_dir / raw)


def default_daily_seed() -> int:
    """Seed that changes once per day (YYYYMMDD)."""
    return int(datetime.now().strftime("%Y%m%d"))


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Build a 32-level procedural Doom II PWAD with corridor-heavy maps "
            "and irregular room shapes."
        )
    )
    parser.add_argument(
        "--output",
        default="rogue_doom.wad",
        help="Output PWAD path (default: rogue_doom.wad in this folder).",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=default_daily_seed(),
        help="Base random seed (default: today's date as YYYYMMDD).",
    )
    parser.add_argument(
        "--trace-log",
        action="store_true",
        help="Emit verbose placement diagnostics to rogue_doom.log.",
    )
    parser.add_argument(
        "--map",
        default="",
        help="Build only one map (e.g. MAP03 or 3).",
    )
    parser.add_argument(
        "--map-count",
        type=int,
        default=DEFAULT_DEVELOPMENT_MAP_COUNT,
        help=(
            "Build only the first N maps from the episode plan "
            f"(default: {DEFAULT_DEVELOPMENT_MAP_COUNT}; full campaign: 32)."
        ),
    )
    parser.add_argument(
        "--safe-map03",
        action="store_true",
        help="Debug mode: skip risky MAP03 internal detail geometry.",
    )
    parser.add_argument(
        "--no-znodes",
        action="store_true",
        help="Skip post-build zdbsp node pass (ZNODES).",
    )
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    global DEBUG_SAFE_MAP03
    DEBUG_SAFE_MAP03 = bool(args.safe_map03)
    script_dir = Path(__file__).resolve().parent
    output = resolve_path(args.output, script_dir).resolve()
    specs = default_episode_plan(base_seed=int(args.seed))
    map_count = max(1, min(32, int(args.map_count)))
    if map_count < len(specs):
        specs = specs[:map_count]
    single_map = str(args.map).strip()
    if single_map:
        map_num: int | None = None
        if single_map.isdigit():
            parsed = int(single_map)
            if 1 <= parsed <= 32:
                map_num = parsed
        else:
            map_num = map_number_from_name(single_map.upper())
        if map_num is None:
            print(f"Invalid --map value: {single_map!r}. Use MAP01..MAP32 or a number 1..32.", file=sys.stderr)
            return 2
        wanted = f"MAP{map_num:02d}"
        specs = [spec for spec in specs if spec.output_map == wanted]
        if not specs:
            print(
                f"Requested map {wanted} not included in current plan. "
                f"(Try increasing --map-count, current={map_count}).",
                file=sys.stderr,
            )
            return 2
    set_trace_logging(bool(args.trace_log))
    clear_trace_log()
    log_event(f"RUN_START argv={argv} trace_log={bool(args.trace_log)}")

    try:
        result = build_pwad(output=output, specs=specs, build_znodes=(not args.no_znodes))
    except Exception as exc:
        log_event(f"RUN_FAIL error={exc!r}")
        print(f"Build failed: {exc}", file=sys.stderr)
        return 1

    log_event(f"RUN_OK output={result.output_path}")
    print(f"Built: {result.output_path}")
    print(f"Compatibility: {result.compatibility_profile}")
    print("Done.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))


