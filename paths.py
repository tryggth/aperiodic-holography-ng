"""
=============================================================================
               ANTIGRAVITY SPLIT-BRAIN WORKSPACE PROTOCOL SPEC
         PROJECT: SPECTRENG (v1.11) - HEREDITARY SIEVE & CONFIG OVERLAY
=============================================================================
"""

import csv
import itertools
import math
import argparse
import sys
import time
import ast

# =====================================================================
# PHASE 1: EXACT DIOPHANTINE ARITHMETIC ENGINES (FROM LEAN 4 CORE)
# =====================================================================

class Z3:
    def __init__(self, u: int, v: int):
        self.u = u
        self.v = v

    def __add__(self, other): 
        return Z3(self.u + other.u, self.v + other.v)
        
    def __sub__(self, other): 
        return Z3(self.u - other.u, self.v - other.v)
        
    def __mul__(self, other):
        return Z3(
            self.u * other.u + 3 * self.v * other.v,
            self.u * other.v + self.v * other.u
        )

    def is_non_neg(self) -> bool:
        if self.u >= 0 and self.v >= 0: return True
        if self.u <= 0 and self.v <= 0: return False
        if self.u < 0 and self.v > 0: return 3 * self.v * self.v >= self.u * self.u
        return self.u * self.u >= 3 * self.v * self.v

    def sign(self) -> int:
        if self.u == 0 and self.v == 0: return 0
        return 1 if self.is_non_neg() else -1

    def to_float(self) -> float:
        return float(self.u) + float(self.v) * math.sqrt(3.0)

    def scale2(self):
        """Magnifies the integer vector by 2 for exact midpoint calculations."""
        return Z3(self.u * 2, self.v * 2)

class Point2D:
    def __init__(self, x: Z3, y: Z3):
        self.x = x
        self.y = y

    def scale2(self):
        return Point2D(self.x.scale2(), self.y.scale2())

class LatticePoint:
    def __init__(self, a: int, b: int, c: int, d: int):
        self.a = a
        self.b = b
        self.c = c
        self.d = d

    def add(self, other):
        return LatticePoint(self.a + other.a, self.b + other.b, self.c + other.c, self.d + other.d)

    def sub(self, other):
        return LatticePoint(self.a - other.a, self.b - other.b, self.c - other.c, self.d - other.d)

    def rot30(self):
        return LatticePoint(-self.d, self.a, self.b + self.d, self.c)

    def to_tuple(self):
        return (self.a, self.b, self.c, self.d)

    def to_point2d(self) -> Point2D:
        return Point2D(Z3(2 * self.a + self.c, self.b), Z3(self.b + 2 * self.d, self.c))


# =====================================================================
# PHASE 2: MONOTILE GEOMETRY & VECTOR INTERSECTION PRUNING
# =====================================================================

SPECTRE_TURNS = [90, -60, 90, 60, 0, 60, -90, 60, 90, 60, -90, 60, 90, -60]
TURN_STEPS = {-90: -3, -60: -2, 0: 0, 60: 2, 90: 3}
STEP_TO_DEG = {-3: -90, -2: -60, 0: 0, 2: 60, 3: 90}
ALLOWED_STEPS = {-3, -2, 0, 2, 3}
SPECTRE_INT_ANGLES = [180 - SPECTRE_TURNS[13]] + [180 - SPECTRE_TURNS[k] for k in range(13)]

def dir_to_vec(d: int) -> LatticePoint:
    pt = LatticePoint(1, 0, 0, 0)
    for _ in range(d % 12): pt = pt.rot30()
    return pt

def cross_product(p1: Point2D, p2: Point2D, p3: Point2D) -> Z3:
    return ((p2.x - p1.x) * (p3.y - p1.y)) - ((p2.y - p1.y) * (p3.x - p1.x))

def segments_intersect(a: Point2D, b: Point2D, c: Point2D, d: Point2D) -> bool:
    s1, s2 = cross_product(a, b, c).sign(), cross_product(a, b, d).sign()
    s3, s4 = cross_product(c, d, a).sign(), cross_product(c, d, b).sign()
    return (s1 * s2 < 0) and (s3 * s4 < 0)

def point_in_polygon(pt: Point2D, poly: list[Point2D]) -> bool:
    count = 0
    for i in range(len(poly) - 1):
        a, b = poly[i], poly[i+1]
        cond1, cond2 = (pt.y - a.y).sign(), (pt.y - b.y).sign()
        if (cond1 >= 0 and cond2 < 0) or (cond2 >= 0 and cond1 < 0):
            cp = cross_product(a, b, pt).sign()
            if (a.y - b.y).sign() < 0:
                if cp > 0: count += 1
            elif cp < 0: count += 1
    return count % 2 == 1

class PlacedTile:
    def __init__(self, origin: LatticePoint, orientation: int):
        self.origin = origin
        self.orientation = orientation
        self.vertices = []
        self.edges = []
        self._build_geometry()

    def _build_geometry(self):
        curr_dir = self.orientation
        curr_pos = self.origin
        self.vertices.append(curr_pos)
        dirs = []
        for t in SPECTRE_TURNS:
            dirs.append(curr_dir)
            curr_dir = (curr_dir + TURN_STEPS[t]) % 12
        for d in dirs:
            next_pos = curr_pos.add(dir_to_vec(d))
            self.edges.append((curr_pos.to_tuple(), next_pos.to_tuple(), d))
            curr_pos = next_pos
            self.vertices.append(curr_pos)

    @staticmethod
    def align_to_path_edge(p_v1: tuple, p_v2: tuple, p_dir: int, tile_edge_idx: int):
        ref_tile = PlacedTile(LatticePoint(0,0,0,0), 0)
        ref_dir = ref_tile.edges[tile_edge_idx][2]
        orientation = (p_dir - ref_dir) % 12
        oriented_ref = PlacedTile(LatticePoint(0,0,0,0), orientation)
        ref_v1 = LatticePoint(*oriented_ref.edges[tile_edge_idx][0])
        target_v1 = LatticePoint(*p_v1)
        origin = target_v1.sub(ref_v1)
        return PlacedTile(origin, orientation)

def polygons_overlap(t1: PlacedTile, t2: PlacedTile) -> bool:
    if t1.origin.to_tuple() == t2.origin.to_tuple() and t1.orientation == t2.orientation:
        return True

    pts1 = [v.to_point2d() for v in t1.vertices]
    pts2 = [v.to_point2d() for v in t2.vertices]

    for i in range(14):
        for j in range(14):
            if segments_intersect(pts1[i], pts1[i+1], pts2[j], pts2[j+1]): 
                return True

    for v in pts1[:-1]:
        if point_in_polygon(v, pts2): return True
    for v in pts2[:-1]:
        if point_in_polygon(v, pts1): return True

    pts1_scaled = [p.scale2() for p in pts1]
    pts2_scaled = [p.scale2() for p in pts2]

    for i in range(14):
        mid = Point2D(pts1[i].x + pts1[i+1].x, pts1[i].y + pts1[i+1].y)
        if point_in_polygon(mid, pts2_scaled): return True

    for j in range(14):
        mid = Point2D(pts2[j].x + pts2[j+1].x, pts2[j].y + pts2[j+1].y)
        if point_in_polygon(mid, pts1_scaled): return True

    return False


# =====================================================================
# PHASE 3: PATH NORMALIZATION & RELATIVE COORDINATE TRACKING ENGINE
# =====================================================================

def trace_absolute_path_vertices(path_steps: tuple) -> list:
    vertices = [LatticePoint(0,0,0,0)]
    curr_pos = LatticePoint(0,0,0,0)
    curr_dir = 0
    
    edges_pool = [0] + list(path_steps)
    for step in edges_pool:
        curr_dir = (curr_dir + step) % 12
        curr_pos = curr_pos.add(dir_to_vec(curr_dir))
        vertices.append(curr_pos)
    return [v.to_tuple() for v in vertices]

def extract_path_fingerprints(tiles: list[PlacedTile], highlighted_verts: list) -> set:
    local_fingerprints = set()
    for tile in tiles:
        local_fingerprints.add((tile.origin.to_tuple(), tile.orientation))
    return local_fingerprints

def render_svg_for_path(path: tuple, solutions: list, filename: str, title: str):
    deg_path_label = [STEP_TO_DEG.get(steps, steps * 30) for steps in path]
    svg_width, svg_height = 1100, 500
    
    svg_content = [
        f'<svg width="{svg_width}" height="{svg_height}" viewBox="0 0 {svg_width} {svg_height}" xmlns="http://www.w3.org/2000/svg">',
        '  <rect width="100%" height="100%" fill="#f9f9f9"/>',
        f'  <text x="550" y="40" font-family="sans-serif" font-size="20" font-weight="bold" text-anchor="middle">{title}</text>',
        f'  <text x="550" y="65" font-family="monospace" font-size="14" fill="#666" text-anchor="middle">Sequence: {deg_path_label}</text>'
    ]
    
    panels = solutions[:2]
    offsets = [270, 830] if len(panels) > 1 else [550]
    
    for panel_idx, tiles in enumerate(panels):
        x_offset = offsets[panel_idx]
        scale = 35
        svg_content.append(f'  <g>')
        label = f"Configuration {panel_idx + 1}" if len(panels) > 1 else "Locked Structural Configuration"
        svg_content.append(f'    <text x="{x_offset}" y="110" font-family="sans-serif" font-size="16" font-weight="bold" text-anchor="middle">{label}</text>')
        
        highlighted_verts = trace_absolute_path_vertices(path)
        v0_lp, v1_lp = LatticePoint(*highlighted_verts[0]), LatticePoint(*highlighted_verts[1])
        p0_2d, p1_2d = v0_lp.to_point2d(), v1_lp.to_point2d()
        x0, y0, x1, y1 = p0_2d.x.to_float(), p0_2d.y.to_float(), p1_2d.x.to_float(), p1_2d.y.to_float()
        heading = math.atan2(y1 - y0, x1 - x0)
        
        def transform_point(lp_tuple):
            p2d = LatticePoint(*lp_tuple).to_point2d()
            gx, gy = p2d.x.to_float(), p2d.y.to_float()
            nx = (gx - x0) * math.cos(heading) + (gy - y0) * math.sin(heading)
            ny = -(gx - x0) * math.sin(heading) + (gy - y0) * math.cos(heading)
            return f"{x_offset + nx * scale},{320 - ny * scale}"
            
        for t_idx, tile in enumerate(tiles):
            poly_pts = [transform_point(v.to_tuple()) for v in tile.vertices]
            fill_color = "rgba(100, 149, 237, 0.25)" if t_idx % 2 == 0 else "rgba(40, 167, 69, 0.25)"
            stroke_color = "#3366cc" if t_idx % 2 == 0 else "#28a745"
            svg_content.append(f'    <polygon points="{" ".join(poly_pts)}" fill="{fill_color}" stroke="{stroke_color}" stroke-width="1.5"/>')
            
        path_pts = [transform_point(v_tuple) for v_tuple in highlighted_verts]
        svg_content.append(f'    <polyline points="{" ".join(path_pts)}" fill="none" stroke="#dc3545" stroke-width="5" stroke-linecap="round" stroke-linejoin="round"/>')
        start_x, start_y = path_pts[0].split(",")
        svg_content.append(f'    <circle cx="{start_x}" cy="{start_y}" r="5" fill="#222"/>')
        svg_content.append(f'  </g>')
        
    svg_content.append('</svg>')
    try:
        with open(filename, "w") as f: 
            f.write("\n".join(svg_content))
        print(f"  [RENDERED] Successfully generated visual study: '{filename}'")
    except Exception as e:
        print(f"  [ERROR] Failed to save SVG: {e}")


# =====================================================================
# PHASE 4: DYNAMIC DIMENSION TOPOLOGICAL LOGIC (WITH STATUS TRACKING)
# =====================================================================

def verify_dual_wedge_filter(tiles: list[PlacedTile], path_steps: tuple, path_verts: list) -> tuple[bool, str]:
    num_turns = len(path_steps)
    for turn_idx in range(num_turns):
        vertex_coords = path_verts[turn_idx + 1]
        turn_deg = STEP_TO_DEG.get(path_steps[turn_idx], path_steps[turn_idx] * 30)
        expected_interior_angle = 180 - turn_deg
        
        cluster_angle_sum = 0
        for single_tile in tiles:
            tile_verts_tuples = [v.to_tuple() for v in single_tile.vertices[:-1]]
            if vertex_coords in tile_verts_tuples:
                v_index = tile_verts_tuples.index(vertex_coords)
                cluster_angle_sum += SPECTRE_INT_ANGLES[v_index]
        
        interior_gap = expected_interior_angle - cluster_angle_sum
        exterior_gap = 360 - cluster_angle_sum
        
        if interior_gap < 0:
            return False, f"Rejected: Boundary Spill (Node {turn_idx+1})"
        if 0 < interior_gap < 90:
            return False, f"Rejected: Unfillable <90° Interior Wedge (Node {turn_idx+1})"
        if 0 < exterior_gap < 90:
            return False, f"Rejected: Unfillable <90° Exterior Wedge (Node {turn_idx+1})"

    return True, "Valid"

def generate_neighborhoods_for_path(path_steps: tuple) -> tuple[list, str]:
    num_edges = len(path_steps) + 1
    path_verts = trace_absolute_path_vertices(path_steps)
    
    path_edges = []
    curr_dir = 0
    edges_pool = [0] + list(path_steps)
    for idx in range(num_edges):
        curr_dir = (curr_dir + edges_pool[idx]) % 12
        path_edges.append((path_verts[idx], path_verts[idx+1], curr_dir))
        
    path_pts2d = [LatticePoint(*v).to_point2d() for v in path_verts]
    
    for i in range(num_edges):
        for j in range(i + 2, num_edges):
            if segments_intersect(path_pts2d[i], path_pts2d[i+1], path_pts2d[j], path_pts2d[j+1]):
                return [], f"Rejected: Path Self-Intersection (Segments {i} & {j})"
                
    valid_neighborhood_layouts = []
    seen_fingerprints = set()
    global_failure_reason = "Rejected: Tile Spatial Collision"

    def bind_edge(edge_idx: int, current_tiles: list):
        nonlocal global_failure_reason
        
        if edge_idx == num_edges:
            unique_tiles_map = {}
            for tile in current_tiles:
                unique_tiles_map[(tile.origin.to_tuple(), tile.orientation)] = tile
            unique_tiles = list(unique_tiles_map.values())
            
            is_valid, wedge_status = verify_dual_wedge_filter(unique_tiles, path_steps, path_verts)
            if is_valid:
                fingerprint = tuple(sorted(unique_tiles_map.keys()))
                if fingerprint not in seen_fingerprints:
                    seen_fingerprints.add(fingerprint)
                    valid_neighborhood_layouts.append(unique_tiles)
            else:
                global_failure_reason = wedge_status
            return

        p_v1, p_v2, p_dir = path_edges[edge_idx]
        
        edge_covered = False
        for tile in current_tiles:
            if any(e[0] == p_v1 and e[1] == p_v2 for e in tile.edges):
                edge_covered = True
                break
                
        if edge_covered:
            bind_edge(edge_idx + 1, current_tiles)
            return

        for tile_edge_idx in range(14):
            candidate_tile = PlacedTile.align_to_path_edge(p_v1, p_v2, p_dir, tile_edge_idx)
            has_collision = False
            for existing_tile in current_tiles:
                if polygons_overlap(candidate_tile, existing_tile):
                    has_collision = True
                    break
            if not has_collision:
                bind_edge(edge_idx + 1, current_tiles + [candidate_tile])

    bind_edge(0, [])
    
    if valid_neighborhood_layouts:
        return valid_neighborhood_layouts, "Valid Boundaries Found"
    else:
        return [], global_failure_reason


# =====================================================================
# PHASE 5: EVALUATION HARNESS & CLI ARCHITECTURE
# =====================================================================

def render_custom_configuration(config_str: str, path_degrees: list = None):
    print(f"\n[CLI OVERRIDE] Rendering Custom Explicit Configuration...")
    try:
        config_data = ast.literal_eval(config_str)
    except Exception as e:
        print(f"  [ERROR] Could not parse configuration string: {e}")
        print(f"  Make sure to wrap the argument in quotes: -c \"[((0,0,0,0),0), ...]\"")
        return

    tiles = []
    for (origin_tup, orientation) in config_data:
        tiles.append(PlacedTile(LatticePoint(*origin_tup), orientation))

    svg_width, svg_height = 1100, 800
    
    svg_content = [
        f'<svg width="{svg_width}" height="{svg_height}" viewBox="0 0 {svg_width} {svg_height}" xmlns="http://www.w3.org/2000/svg">',
        '  <rect width="100%" height="100%" fill="#f9f9f9"/>',
        f'  <text x="550" y="40" font-family="sans-serif" font-size="20" font-weight="bold" text-anchor="middle">Custom Explicit Configuration</text>'
    ]
    
    scale = 35
    x_offset, y_offset = 550, 400

    def transform_point(lp_tuple):
        p2d = LatticePoint(*lp_tuple).to_point2d()
        gx, gy = p2d.x.to_float(), p2d.y.to_float()
        return f"{x_offset + gx * scale},{y_offset - gy * scale}"

    svg_content.append('  <g>')
    for t_idx, tile in enumerate(tiles):
        poly_pts = [transform_point(v.to_tuple()) for v in tile.vertices]
        fill_color = "rgba(100, 149, 237, 0.25)" if t_idx % 2 == 0 else "rgba(40, 167, 69, 0.25)"
        stroke_color = "#3366cc" if t_idx % 2 == 0 else "#28a745"
        svg_content.append(f'    <polygon points="{" ".join(poly_pts)}" fill="{fill_color}" stroke="{stroke_color}" stroke-width="1.5"/>')
    svg_content.append('  </g>')

    # Optional Overlay Path Logic
    if path_degrees:
        try:
            step_path = tuple(deg // 30 for deg in path_degrees)
            highlighted_verts = trace_absolute_path_vertices(step_path)
            path_pts = [transform_point(v_tuple) for v_tuple in highlighted_verts]
            svg_content.append(f'  <g>')
            svg_content.append(f'    <polyline points="{" ".join(path_pts)}" fill="none" stroke="#dc3545" stroke-width="5" stroke-linecap="round" stroke-linejoin="round"/>')
            start_x, start_y = path_pts[0].split(",")
            svg_content.append(f'    <circle cx="{start_x}" cy="{start_y}" r="5" fill="#222"/>')
            svg_content.append(f'  </g>')
            svg_content.append(f'  <text x="550" y="65" font-family="monospace" font-size="14" fill="#666" text-anchor="middle">Overlay Path: {path_degrees}</text>')
        except Exception as e:
            print(f"  [WARNING] Failed to overlay path configuration: {e}")

    svg_content.append('</svg>')
    filename = "spectre_custom_layout.svg"
    with open(filename, "w") as f: 
        f.write("\n".join(svg_content))
    print(f"  [RENDERED] Successfully generated visual study: '{filename}'\n")

def evaluate_single_target(sequence_degrees: list):
    print(f"\n[CLI OVERRIDE] Deep-Scanning Custom Target Sequence: {sequence_degrees}")
    
    try:
        step_path = tuple(deg // 30 for deg in sequence_degrees)
    except Exception:
        print("  [ERROR] Invalid format. Sequence degrees must be multiples of 30.")
        return

    matching_configurations, status_msg = generate_neighborhoods_for_path(step_path)
    
    if not matching_configurations:
        print(f"  ❌ [RESULT] Geometrically Invalid: {status_msg}")
        return
        
    path_verts = trace_absolute_path_vertices(step_path)
    all_local_fingerprints = [extract_path_fingerprints(tiles, path_verts) for tiles in matching_configurations]
    
    frozen_tiles = all_local_fingerprints[0]
    for coordinate_set in all_local_fingerprints[1:]:
        frozen_tiles = frozen_tiles.intersection(coordinate_set)
        
    forced_count = len(frozen_tiles)
    total_layouts = len(matching_configurations)
    
    if forced_count >= 1:
        print(f"  ✅ [RESULT] Absolute Holographic Lock!")
        print(f"     -> The structure forces {forced_count} rigid, completely stationary anchor tile(s).")
        print(f"     -> Permitted exterior configuration variance: {total_layouts} layout(s).")
        render_svg_for_path(step_path, matching_configurations, f"spectre_custom_lock.svg", "CLI Explicit Lock Analysis")
    else:
        print(f"  ⚠️ [RESULT] True Ambiguity Deviation!")
        print(f"     -> Path allows {total_layouts} valid physical structures with ZERO shared anchor tiles.")
        print(f"     -> [DUMPING CONFIGURATIONS]")
        for i, config_set in enumerate(all_local_fingerprints):
            sorted_tiles = sorted(list(config_set))
            print(f"        Layout {i+1}: {sorted_tiles}")
        render_svg_for_path(step_path, matching_configurations, f"spectre_custom_ambiguity.svg", "CLI Explicit Ambiguity Analysis")
    print("")

def execute_hereditary_sieve(max_n=5):
    print(f"\n[INIT] Booting Hereditary Sieve Architecture (Target: Length {max_n})...")
    
    filename = f"spectre_path_locks_hereditary.csv"
    file = open(filename, mode='w', newline='')
    writer = csv.writer(file)
    writer.writerow(["Length", "Path_ID", "Sequence_Degrees", "Is_Valid_Boundary", "Holographic_Lock_Status", "Forced_Tile_Count", "Ambiguous_Layout_Dumps"])
    
    turn_steps_pool = [-3, -2, 0, 2, 3]
    forbidden_substrings = set()
    valid_paths = [(s,) for s in turn_steps_pool]
    
    global_start = time.time()
    
    for current_n in range(2, max_n + 1):
        level_start = time.time()
        
        next_valid_paths = []
        stats = {"generated": 0, "pruned": 0, "evaluated": 0, "invalid": 0, "ambiguous": 0, "locked": 0}
        ambiguous_cases = []
        
        for prefix in valid_paths:
            for turn in turn_steps_pool:
                candidate_path = prefix + (turn,)
                stats["generated"] += 1
                
                is_pruned = False
                for i in range(1, len(candidate_path)):
                    if candidate_path[i:] in forbidden_substrings:
                        is_pruned = True
                        break
                        
                if is_pruned:
                    stats["pruned"] += 1
                    deg_list = [STEP_TO_DEG[s] for s in candidate_path]
                    human_readable_sequence = ", ".join(f"{d}°" for d in deg_list)
                    path_label = f"PATH_SEQ_{current_n}_{stats['generated']:05d}"
                    writer.writerow([current_n, path_label, f"[{human_readable_sequence}]", "FALSE", "Rejected: Hereditary Prune (Forbidden Substring)", 0, ""])
                    continue
                    
                stats["evaluated"] += 1
                matching_configurations, status_msg = generate_neighborhoods_for_path(candidate_path)
                
                deg_list = [STEP_TO_DEG[s] for s in candidate_path]
                human_readable_sequence = ", ".join(f"{d}°" for d in deg_list)
                path_label = f"PATH_SEQ_{current_n}_{stats['generated']:05d}"
                
                if not matching_configurations:
                    forbidden_substrings.add(candidate_path)
                    stats["invalid"] += 1
                    writer.writerow([current_n, path_label, f"[{human_readable_sequence}]", "FALSE", status_msg, 0, ""])
                    continue
                    
                next_valid_paths.append(candidate_path)
                
                path_verts = trace_absolute_path_vertices(candidate_path)
                all_local_fingerprints = [extract_path_fingerprints(tiles, path_verts) for tiles in matching_configurations]
                
                frozen_tiles = all_local_fingerprints[0]
                for coordinate_set in all_local_fingerprints[1:]:
                    frozen_tiles = frozen_tiles.intersection(coordinate_set)
                    
                forced_count = len(frozen_tiles)
                ambiguous_dump = ""
                
                if forced_count >= 1:
                    stats["locked"] += 1
                    lock_status = f"Absolute Holographic Lock: Form forces {forced_count} tile(s) to be completely stationary"
                else:
                    stats["ambiguous"] += 1
                    ambiguous_cases.append((candidate_path, matching_configurations))
                    lock_status = f"True Ambiguity: No tiles are shared across all {len(matching_configurations)} layouts"
                    
                    dump_parts = []
                    for idx, config_set in enumerate(all_local_fingerprints):
                        sorted_tiles = sorted(list(config_set))
                        dump_parts.append(f"Layout {idx+1}: {sorted_tiles}")
                    ambiguous_dump = " | ".join(dump_parts)
                
                writer.writerow([current_n, path_label, f"[{human_readable_sequence}]", "TRUE", lock_status, forced_count, ambiguous_dump])
        
        print(f"\n================ APERIODIC HOLOGRAPHY REPORT (N={current_n}) ================")
        print(f" Boundary Length Evaluated        : {current_n} Turns")
        print(f" Total Path Sequences Evaluated   : {stats['evaluated']:,} (Out of {stats['generated']:,} permutations)")
        print(f" Geometrically Invalid Boundaries : {stats['invalid']:,}")
        print(f" Absolute Holographic Locks       : {stats['locked']:,}")
        print(f" True Ambiguity Deviations        : {stats['ambiguous']:,}")
        print(f"--------------------------------------------------------------")
        print(f" Level Processing Time            : {time.time() - level_start:.2f} seconds")
        print(f" Guillotined by Sieve             : {stats['pruned']:,} (Bypassed Physics Engine)")
        print(f" Valid Paths Surviving to N+1     : {len(next_valid_paths):,}")
        print(f"==============================================================\n")
        
        valid_paths = next_valid_paths

    file.close()
    total_time = time.time() - global_start
    print(f"\n[COMPLETE] Hereditary Sieve reached N={max_n}")
    print(f" Total Global Execution Time : {total_time:.2f} seconds")
    print(f" Spreadsheet successfully saved to: '{filename}'")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Antigravity CLI - SpectreNG Holographic Sieve")
    parser.add_argument("-s", "--sequence", type=int, nargs="+", 
                        help="Test a specific turn sequence explicitly (e.g., -s 90 -60 60). Skips CSV generation.")
    parser.add_argument("-n", "--length", type=int, default=5,
                        help="Number of turns to evaluate for the full combinatorial sieve (default: 5).")
    parser.add_argument("-c", "--config", type=str,
                        help="Render an SVG for a specific configuration tuple string.")
    parser.add_argument("-p", "--path", type=int, nargs="+",
                        help="Optional turn sequence degrees (e.g., -p -90 60 -90) to overlay in red when using -c.")
    
    args = parser.parse_args() if len(sys.argv) > 1 else parser.parse_args([])
    
    if args.config:
        render_custom_configuration(args.config, path_degrees=args.path)
    elif args.sequence:
        evaluate_single_target(args.sequence)
    else:
        execute_hereditary_sieve(max_n=args.length)