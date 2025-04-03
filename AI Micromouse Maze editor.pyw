import tkinter as tk
from tkinter import Canvas, Frame, Button, Label, Entry, messagebox, filedialog, StringVar, DoubleVar
import math
import json
import random # For generation
from collections import deque
import heapq
import time

# --- Configuration Constants ---
GRID_SIZE = 16
DEFAULT_CELL_VISUAL_SIZE_PX = 25
MARGIN = 25
POST_RADIUS = 2
WALL_THICKNESS = 2
ROUTE_WIDTH = 2 # Keep a slight width to see overlapping colors if possible
CELL_PHYSICAL_SIZE_M = 0.18 # 18 cm per cell
MAZE_GENERATION_LOOP_PROBABILITY = 0.15 # Chance to remove an extra wall to create loops

# Colors
COLOR_BACKGROUND = "white"; COLOR_POST = "black"; COLOR_WALL = "blue"
COLOR_START = "lightgreen"; COLOR_GOAL = "lightblue"; COLOR_GRID_LINE = "#eee"
COLOR_ROUTE_LEFT = "red"; COLOR_ROUTE_SHORTEST = "purple"
COLOR_ROUTE_STRAIGHTEST = "darkorange"; COLOR_ROUTE_DIAGONAL = "forest green"
COLOR_KEY_SWATCH_BORDER = "#555"
COLOR_HIGHLIGHT_OPEN = "yellow" # Color for open cells

# Turn Penalties
DEFAULT_TURN_WEIGHT_STRAIGHTEST = 1.0
TURN_PENALTY_SHORTEST = 0.01
TURN_PENALTY_DIAGONAL = 1.0 # Turn penalty for diagonal path

# --- Directions ---
N, NE, E, SE, S, SW, W, NW = 0, 1, 2, 3, 4, 5, 6, 7
DR8 = [-1,-1, 0, 1, 1, 1, 0,-1]; DC8 = [ 0, 1, 1, 1, 0,-1,-1,-1]
SQRT2 = math.sqrt(2.0)
MOVE_COST = [1.0, SQRT2, 1.0, SQRT2, 1.0, SQRT2, 1.0, SQRT2]
N4, E4, S4, W4 = 0, 1, 2, 3 # Indices for 4-dir arrays/logic
DR4 = [-1, 0, 1, 0]; DC4 = [0, 1, 0, -1]

class MazeEditor:
    def __init__(self, master):
        self.master = master
        self.master.title("Micromouse Maze Editor (16x16)")

        self.cell_visual_size_px = DEFAULT_CELL_VISUAL_SIZE_PX
        self.last_width = 0; self.last_height = 0
        self.resize_timer = None

        self.h_walls = [[False for _ in range(GRID_SIZE)] for _ in range(GRID_SIZE + 1)]
        self.v_walls = [[False for _ in range(GRID_SIZE + 1)] for _ in range(GRID_SIZE)]
        self.initialize_outer_walls()

        # Route Data
        self.route_path_left = []; self.route_path_shortest = []
        self.route_path_straightest = []; self.route_path_diagonal = []
        self.msg_left=""; self.msg_shortest=""; self.msg_straightest=""; self.msg_diagonal=""

        self.goal_cells = {
            (GRID_SIZE//2-1, GRID_SIZE//2-1), (GRID_SIZE//2-1, GRID_SIZE//2),
            (GRID_SIZE//2, GRID_SIZE//2-1), (GRID_SIZE//2, GRID_SIZE//2)
        }
        self.start_pos_lh = (GRID_SIZE - 1, 0, N4)
        self.start_cell = (GRID_SIZE - 1, 0)

        self.turn_weight_var = DoubleVar(value=DEFAULT_TURN_WEIGHT_STRAIGHTEST)
        self.turn_weight_var.trace_add("write", self.on_turn_weight_change)

        # Route Visibility Toggles
        self.show_route_left_var = tk.BooleanVar(value=True)
        self.show_route_shortest_var = tk.BooleanVar(value=True)
        self.show_route_straightest_var = tk.BooleanVar(value=True)
        self.show_route_diagonal_var = tk.BooleanVar(value=True)
        self.highlight_open_cells_var = tk.BooleanVar(value=False)

        self._setup_gui()
        self._create_color_key()

        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.master.bind("<Configure>", self.schedule_resize)

        self.master.update_idletasks()
        self.handle_resize(self.master.winfo_width(), self.master.winfo_height())
        self.reset_maze()

    # --- Dynamic Size Calculation Properties ---
    @property
    def click_tolerance(self): return self.cell_visual_size_px * 0.4
    # Removed offset properties

    # --- GUI Setup ---
    def _setup_gui(self):
        self.master.rowconfigure(1, weight=1); self.master.columnconfigure(0, weight=1)
        top_control_frame = Frame(self.master)
        top_control_frame.grid(row=0, column=0, sticky="ew", pady=(10, 0), padx=10)
        Button(top_control_frame, text="Reset Maze", command=self.reset_maze).pack(side=tk.LEFT, padx=5)
        Button(top_control_frame, text="Generate Maze", command=self.generate_maze).pack(side=tk.LEFT, padx=5)
        Button(top_control_frame, text="Save Maze", command=self.save_maze).pack(side=tk.LEFT, padx=5)
        Button(top_control_frame, text="Load Maze", command=self.load_maze).pack(side=tk.LEFT, padx=5)
        right_controls_frame = Frame(top_control_frame)
        right_controls_frame.pack(side=tk.RIGHT, padx=10)
        weight_frame = Frame(right_controls_frame); weight_frame.pack(side=tk.LEFT, padx=5)
        Label(weight_frame, text="Turn W:").pack(side=tk.LEFT)
        vcmd = (self.master.register(self.validate_float_entry), '%P')
        self.turn_weight_entry = Entry(weight_frame, textvariable=self.turn_weight_var, width=5, validate='key', validatecommand=vcmd)
        self.turn_weight_entry.pack(side=tk.LEFT, padx=(2, 0))
        highlight_frame = Frame(right_controls_frame); highlight_frame.pack(side=tk.LEFT, padx=5)
        self.highlight_checkbutton = tk.Checkbutton(highlight_frame, text="Highlight Open", variable=self.highlight_open_cells_var, command=self.find_and_draw_routes)
        self.highlight_checkbutton.pack(side=tk.LEFT)
        initial_canvas_width = 2*MARGIN+GRID_SIZE*self.cell_visual_size_px
        initial_canvas_height = 2*MARGIN+GRID_SIZE*self.cell_visual_size_px
        self.canvas = Canvas(self.master, width=initial_canvas_width, height=initial_canvas_height, bg=COLOR_BACKGROUND)
        self.canvas.grid(row=1, column=0, sticky="nsew", pady=(5, 5), padx=10)
        self.key_frame = Frame(self.master, bd=1, relief=tk.GROOVE)
        self.key_frame.grid(row=2, column=0, sticky="ew", pady=(0, 5), padx=10)
        self.status_label = Label(self.master, text="Initializing...", bd=1, relief=tk.SUNKEN, anchor=tk.W)
        self.status_label.grid(row=3, column=0, sticky="ew", ipady=2)

    def _create_color_key(self):
        self.key_frame.columnconfigure(0, weight=1); self.key_frame.columnconfigure(1, weight=1)
        self.key_frame.columnconfigure(2, weight=1); self.key_frame.columnconfigure(3, weight=1)
        font_size = 8; swatch_size = 12
        def create_key_entry(parent, col, color, var):
            frame = Frame(parent); frame.grid(row=0, column=col, sticky='w', padx=3, pady=0)
            toggle = tk.Checkbutton(frame, variable=var, command=self.draw_current_routes, pady=0, padx=0)
            toggle.pack(side=tk.LEFT)
            Label(frame, text="", width=2, relief=tk.RAISED, bd=1, bg=color).pack(side=tk.LEFT, padx=(0,2))
            label_widget = Label(frame, text="--", anchor='w', font=("TkDefaultFont", font_size))
            label_widget.pack(side=tk.LEFT, fill='x', expand=True)
            return label_widget
        self.key_label_left = create_key_entry(self.key_frame, 0, COLOR_ROUTE_LEFT, self.show_route_left_var)
        self.key_label_shortest = create_key_entry(self.key_frame, 1, COLOR_ROUTE_SHORTEST, self.show_route_shortest_var)
        self.key_label_straightest = create_key_entry(self.key_frame, 2, COLOR_ROUTE_STRAIGHTEST, self.show_route_straightest_var)
        self.key_label_diagonal = create_key_entry(self.key_frame, 3, COLOR_ROUTE_DIAGONAL, self.show_route_diagonal_var)

    def validate_float_entry(self, P):
        if P == "" or P == ".": return True
        if P == "-": return True
        if P.startswith("-") and P.count('-') > 1: return False
        if P.startswith("-") and P == "-.": return True
        try:
            parts = P.split('.');
            if len(parts) > 2: return False
            if not parts[0].lstrip('-').isdigit() and parts[0].lstrip('-') != "": return False
            if len(parts) > 1 and not parts[1].isdigit() and parts[1] != "": return False
            return True
        except Exception: return False

    # --- Resizing Logic ---
    def schedule_resize(self, event=None):
        if event and event.widget != self.master: return
        if self.resize_timer is not None: self.master.after_cancel(self.resize_timer)
        self.resize_timer = self.master.after(100, self._perform_resize_check)
    def _perform_resize_check(self):
         self.resize_timer = None
         current_width = self.master.winfo_width(); current_height = self.master.winfo_height()
         if abs(current_width - self.last_width) > 5 or abs(current_height - self.last_height) > 5:
             self.handle_resize(current_width, current_height)
    def handle_resize(self, width, height):
        self.last_width = width; self.last_height = height
        try:
             canvas_width = self.canvas.winfo_width(); canvas_height = self.canvas.winfo_height()
             if canvas_width <= 1 or canvas_height <= 1: raise ValueError
        except Exception:
             estimated_control_height = 90
             canvas_width = width - 20; canvas_height = height - estimated_control_height - 20
        cell_size_w = (canvas_width - 2 * MARGIN) / GRID_SIZE
        cell_size_h = (canvas_height - 2 * MARGIN) / GRID_SIZE
        new_cell_size = max(5, int(min(cell_size_w, cell_size_h)))
        if new_cell_size != self.cell_visual_size_px:
            self.cell_visual_size_px = new_cell_size
            self.find_and_draw_routes()

    # --- Maze Manipulation ---
    def initialize_outer_walls(self):
        for c in range(GRID_SIZE): self.h_walls[0][c] = self.h_walls[GRID_SIZE][c] = True
        for r in range(GRID_SIZE): self.v_walls[r][0] = self.v_walls[r][GRID_SIZE] = True

    def reset_maze(self):
        for r in range(1, GRID_SIZE):
            for c in range(GRID_SIZE): self.h_walls[r][c] = False
        for r in range(GRID_SIZE):
            for c in range(1, GRID_SIZE): self.v_walls[r][c] = False
        self.find_and_draw_routes()
        self.update_status("Maze reset to empty.")

    def _initialize_all_walls(self):
        for r in range(1, GRID_SIZE):
            for c in range(GRID_SIZE): self.h_walls[r][c] = True
        for r in range(GRID_SIZE):
            for c in range(1, GRID_SIZE): self.v_walls[r][c] = True

    def clear_routes(self):
        self.route_path_left = []; self.route_path_shortest = []
        self.route_path_straightest = []; self.route_path_diagonal = []
        self.canvas.delete("route_left", "route_shortest", "route_straightest", "route_diagonal")

    # --- Coordinate Conversion ---
    def cell_to_pixel(self, r, c):
        x = MARGIN + c * self.cell_visual_size_px; y = MARGIN + r * self.cell_visual_size_px
        return x, y
    def cell_center_to_pixel(self, r, c, offset_x=0, offset_y=0): # Offset args kept for compatibility, but not used now
        x = MARGIN + (c + 0.5) * self.cell_visual_size_px + offset_x
        y = MARGIN + (r + 0.5) * self.cell_visual_size_px + offset_y
        return x, y
    def pixel_to_cell(self, x, y):
        if self.cell_visual_size_px <= 0: return (0,0)
        x_adj = x - MARGIN; y_adj = y - MARGIN
        c = int(x_adj / self.cell_visual_size_px); r = int(y_adj / self.cell_visual_size_px)
        c = max(0, min(c, GRID_SIZE - 1)); r = max(0, min(r, GRID_SIZE - 1))
        return r, c

    # --- Wall Handling & Events ---
    def has_wall(self, r, c, direction4):
        if not (0 <= r < GRID_SIZE and 0 <= c < GRID_SIZE): return True
        if direction4 == N4: return self.h_walls[r][c]
        elif direction4 == E4: return self.v_walls[r][c+1]
        elif direction4 == S4: return self.h_walls[r+1][c]
        elif direction4 == W4: return self.v_walls[r][c]
        return True
    def _can_move_diag(self, r, c, diag_direction):
        if diag_direction == NE: return not self.has_wall(r, c, N4) and not self.has_wall(r, c, E4)
        elif diag_direction == SE: return not self.has_wall(r, c, S4) and not self.has_wall(r, c, E4)
        elif diag_direction == SW: return not self.has_wall(r, c, S4) and not self.has_wall(r, c, W4)
        elif diag_direction == NW: return not self.has_wall(r, c, N4) and not self.has_wall(r, c, W4)
        return False
    def get_wall_from_coords(self, click_x, click_y):
        min_dist_sq = (self.click_tolerance ** 2) + 1; closest_wall = None
        cell_size = self.cell_visual_size_px;
        if cell_size <=0: return None
        r_approx_h=round((click_y-MARGIN)/cell_size); c_approx_h=int((click_x-MARGIN)/cell_size)
        for r_check in [r_approx_h]:
            if 0<=r_check<=GRID_SIZE:
                for c_check in range(max(0,c_approx_h-1),min(GRID_SIZE,c_approx_h+2)):
                    if 0<=c_check<GRID_SIZE:
                        wall_mid_x=MARGIN+(c_check+0.5)*cell_size; wall_mid_y=MARGIN+r_check*cell_size
                        d2=(click_x-wall_mid_x)**2+(click_y-wall_mid_y)**2
                        if d2<min_dist_sq: min_dist_sq=d2; closest_wall=('h',r_check,c_check)
        c_approx_v=round((click_x-MARGIN)/cell_size); r_approx_v=int((click_y-MARGIN)/cell_size)
        for c_check in [c_approx_v]:
            if 0<=c_check<=GRID_SIZE:
                for r_check in range(max(0,r_approx_v-1),min(GRID_SIZE,r_approx_v+2)):
                    if 0<=r_check<GRID_SIZE:
                        wall_mid_x=MARGIN+c_check*cell_size; wall_mid_y=MARGIN+(r_check+0.5)*cell_size
                        d2=(click_x-wall_mid_x)**2+(click_y-wall_mid_y)**2
                        if d2<min_dist_sq: min_dist_sq=d2; closest_wall=('v',r_check,c_check)
        if min_dist_sq<=(self.click_tolerance**2):
            wall_type, r, c = closest_wall
            if wall_type=='h' and (r==0 or r==GRID_SIZE): return None
            if wall_type=='v' and (c==0 or c==GRID_SIZE): return None
            return closest_wall
        return None
    def on_canvas_click(self, event):
        wall_info = self.get_wall_from_coords(event.x, event.y)
        if wall_info:
            wall_type, r, c = wall_info; toggled = False
            if wall_type == 'h': self.h_walls[r][c] = not self.h_walls[r][c]; toggled = True
            elif wall_type == 'v': self.v_walls[r][c] = not self.v_walls[r][c]; toggled = True
            if toggled:
                self.find_and_draw_routes()
                self.update_status(f"Wall {'H' if wall_type=='h' else 'V'}({r},{c}) toggled.")
    def on_turn_weight_change(self, *args):
         try:
             current_value = self.turn_weight_var.get()
             self.find_and_draw_routes()
             self.update_status("Turn weight changed.")
         except tk.TclError: pass

    # --- Drawing ---
    def draw_maze(self):
        cell_size = self.cell_visual_size_px
        if cell_size <= 0: return
        self.canvas.delete("all")
        start_r, start_c = self.start_cell
        highlight_on = self.highlight_open_cells_var.get()
        for r in range(GRID_SIZE):
            for c in range(GRID_SIZE):
                x0,y0=self.cell_to_pixel(r,c); x1,y1=x0+cell_size,y0+cell_size
                fill_color = COLOR_BACKGROUND
                is_goal = (r, c) in self.goal_cells
                if (r,c)==(start_r,start_c): fill_color = COLOR_START
                elif is_goal: fill_color = COLOR_GOAL
                elif highlight_on:
                     wall_n = self.has_wall(r, c, N4); wall_e = self.has_wall(r, c, E4)
                     wall_s = self.has_wall(r, c, S4); wall_w = self.has_wall(r, c, W4)
                     if not wall_n and not wall_e and not wall_s and not wall_w:
                         fill_color = COLOR_HIGHLIGHT_OPEN
                self.canvas.create_rectangle(x0, y0, x1, y1, fill=fill_color, outline=COLOR_GRID_LINE, tags="cell")

        # Draw Start Arrow (correctly uses cell_center_to_pixel without extra args)
        arrow_center_x, arrow_base_y = self.cell_center_to_pixel(start_r,start_c)
        arrow_tip_y = arrow_base_y - cell_size * 0.4 # Calculate tip relative to base
        arrow_width = max(1, int(cell_size * 0.1))
        self.canvas.create_line(arrow_center_x,arrow_base_y,arrow_center_x,arrow_tip_y,arrow=tk.LAST,fill="black",width=arrow_width,tags="start_arrow")

        for r_wall in range(GRID_SIZE + 1):
            for c_wall in range(GRID_SIZE):
                if self.h_walls[r_wall][c_wall]:
                    x0,y0=self.cell_to_pixel(r_wall,c_wall); x1=x0+cell_size; y1=y0
                    self.canvas.create_line(x0, y0, x1, y1, fill=COLOR_WALL, width=WALL_THICKNESS, tags="wall")
        for r_wall in range(GRID_SIZE):
            for c_wall in range(GRID_SIZE + 1):
                 if self.v_walls[r_wall][c_wall]:
                    x0,y0=self.cell_to_pixel(r_wall,c_wall); x1=x0; y1=y0+cell_size
                    self.canvas.create_line(x0, y0, x1, y1, fill=COLOR_WALL, width=WALL_THICKNESS, tags="wall")
        post_rad = POST_RADIUS
        for r_post in range(GRID_SIZE + 1):
            for c_post in range(GRID_SIZE + 1):
                x_center = MARGIN + c_post * cell_size; y_center = MARGIN + r_post * cell_size
                self.canvas.create_oval(x_center-post_rad,y_center-post_rad,x_center+post_rad,y_center+post_rad, fill=COLOR_POST, outline=COLOR_POST, tags="post")

    # Removed _get_segment_offset

    def draw_current_routes(self):
        """Draws all stored routes center-to-center, respects visibility toggles."""
        self.canvas.delete("route_left", "route_shortest", "route_straightest", "route_diagonal")

        visibility_map = {
            "route_left": self.show_route_left_var,
            "route_shortest": self.show_route_shortest_var,
            "route_diagonal": self.show_route_diagonal_var,
            "route_straightest": self.show_route_straightest_var
        }
        line_options = {'width': ROUTE_WIDTH, 'capstyle': tk.ROUND}

        paths_colors_tags = [
            (self.route_path_shortest, COLOR_ROUTE_SHORTEST, "route_shortest"),
            (self.route_path_diagonal, COLOR_ROUTE_DIAGONAL, "route_diagonal"),
            (self.route_path_straightest, COLOR_ROUTE_STRAIGHTEST, "route_straightest"),
            (self.route_path_left, COLOR_ROUTE_LEFT, "route_left"),
        ]

        for path, color, tag in paths_colors_tags:
            visibility_var = visibility_map.get(tag)
            if not visibility_var or not visibility_var.get(): continue
            if len(path) < 2: continue

            # --- Draw ALL paths center-to-center ---
            for i in range(len(path) - 1):
                r1, c1 = path[i]; r2, c2 = path[i+1]
                x1c, y1c = self.cell_center_to_pixel(r1, c1) # No offset
                x2c, y2c = self.cell_center_to_pixel(r2, c2) # No offset
                self.canvas.create_line(x1c, y1c, x2c, y2c, fill=color, tags=tag, **line_options)
            # --- No connector logic needed ---

    # --- Path Distance Calculation ---
    def _calculate_path_distance(self, path):
        distance = 0.0
        if len(path) < 2: return 0.0
        for i in range(len(path) - 1):
            r1, c1 = path[i]; r2, c2 = path[i+1]
            dr = abs(r1 - r2); dc = abs(c1 - c2)
            if dr + dc == 1: distance += CELL_PHYSICAL_SIZE_M # Orthogonal
            elif dr == 1 and dc == 1: distance += CELL_PHYSICAL_SIZE_M * SQRT2 # Diagonal
        return distance

    # --- Route Finding ---
    def find_and_draw_routes(self):
        path_left, msg_left_base = self._calculate_left_hand_path()
        path_shortest, msg_shortest_base = self._calculate_dijkstra_path(TURN_PENALTY_SHORTEST)
        current_turn_weight = DEFAULT_TURN_WEIGHT_STRAIGHTEST
        try:
            current_turn_weight = self.turn_weight_var.get()
            if current_turn_weight < 0: current_turn_weight = 0
        except tk.TclError: self.turn_weight_var.set(DEFAULT_TURN_WEIGHT_STRAIGHTEST)
        path_straightest, msg_straightest_base = self._calculate_dijkstra_path(current_turn_weight)
        path_diagonal, msg_diagonal_base = self._calculate_dijkstra_diag_path(TURN_PENALTY_DIAGONAL)
        dist_left = self._calculate_path_distance(path_left)
        dist_shortest = self._calculate_path_distance(path_shortest)
        dist_straightest = self._calculate_path_distance(path_straightest)
        dist_diagonal = self._calculate_path_distance(path_diagonal)
        self.msg_left = f"{msg_left_base}, {dist_left:.2f}m" if path_left else msg_left_base
        self.msg_shortest = f"{msg_shortest_base}, {dist_shortest:.2f}m" if path_shortest else msg_shortest_base
        self.msg_straightest = f"{msg_straightest_base}, {dist_straightest:.2f}m" if path_straightest else msg_straightest_base
        self.msg_diagonal = f"{msg_diagonal_base}, {dist_diagonal:.2f}m" if path_diagonal else msg_diagonal_base
        self.route_path_left = path_left; self.route_path_shortest = path_shortest
        self.route_path_straightest = path_straightest; self.route_path_diagonal = path_diagonal
        self.draw_maze(); self.draw_current_routes()
        w_text = f"(w={current_turn_weight:.2f})"
        self.key_label_left.config(text=f"L: {self.msg_left}")
        self.key_label_shortest.config(text=f"S: {self.msg_shortest}")
        self.key_label_straightest.config(text=f"St {w_text}: {self.msg_straightest}")
        self.key_label_diagonal.config(text=f"Diag: {self.msg_diagonal}")

    def _calculate_left_hand_path(self):
        r, c, direction = self.start_pos_lh # Use N4
        path = [(r, c)]; visited_states = set([(r, c, direction)])
        max_steps = GRID_SIZE * GRID_SIZE * 5; step_count = 0; found_goal = False
        while step_count < max_steps:
            step_count += 1
            if (r, c) in self.goal_cells: found_goal = True; break
            left_dir4 = (direction - 1 + 4) % 4
            wall_left = self.has_wall(r, c, left_dir4)
            next_r, next_c, next_dir = r, c, direction
            if not wall_left:
                next_dir = left_dir4; next_r += DR4[next_dir]; next_c += DC4[next_dir]
            else:
                wall_ahead = self.has_wall(r, c, direction)
                if not wall_ahead: next_r += DR4[direction]; next_c += DC4[direction]
                else: next_dir = (direction + 1) % 4
            if not (0 <= next_r < GRID_SIZE and 0 <= next_c < GRID_SIZE):
                next_dir = (direction + 1) % 4; next_r, next_c = r, c
            r, c, direction = next_r, next_c, next_dir
            current_state = (r, c, direction)
            if current_state in visited_states:
                 if (r, c) in self.goal_cells: found_goal = True; break
                 return path, f"Loop ({step_count} steps)"
            visited_states.add(current_state)
            if path[-1] != (r,c): path.append((r, c))
        if found_goal: return path, f"Goal ({len(path) - 1} steps)"
        elif step_count >= max_steps: return path, f"Max steps ({max_steps})"
        else: return path, "End"

    def _calculate_dijkstra_path(self, turn_weight): # Orthogonal only
        start_node = self.start_cell
        pq = [(0.0, 0.0, 0, start_node[0], start_node[1], None, [start_node])]
        visited = {}
        while pq:
            priority, dist, turns, r, c, arr_dir, path = heapq.heappop(pq)
            if (r, c) in self.goal_cells: return path, f"Goal ({dist:.0f}c, {turns}t)"
            visited_key = (r, c, arr_dir)
            if visited_key in visited and visited[visited_key] <= priority: continue
            visited[visited_key] = priority
            for next_dir4 in range(4):
                if not self.has_wall(r, c, next_dir4):
                    next_r, next_c = r + DR4[next_dir4], c + DC4[next_dir4]
                    if not (0 <= next_r < GRID_SIZE and 0 <= next_c < GRID_SIZE): continue
                    new_dist = dist + 1.0
                    turn_inc = 1 if arr_dir is not None and next_dir4 != arr_dir else 0
                    new_turns = turns + turn_inc
                    new_priority = new_dist + turn_weight * float(new_turns)
                    next_visited_key = (next_r, next_c, next_dir4)
                    if next_visited_key not in visited or new_priority < visited[next_visited_key]:
                        new_path = path + [(next_r, next_c)]
                        heapq.heappush(pq, (new_priority, new_dist, new_turns, next_r, next_c, next_dir4, new_path))
        return [], "Unreachable"

    def _calculate_dijkstra_diag_path(self, turn_weight): # Allows diagonals
        start_node = self.start_cell
        pq = [(0.0, 0.0, 0, start_node[0], start_node[1], None, [start_node])]
        visited = {}
        while pq:
            priority, dist, turns, r, c, arr_dir8, path = heapq.heappop(pq)
            if (r, c) in self.goal_cells: return path, f"Goal ({dist:.1f} cost, {turns}t)"
            visited_key = (r, c, arr_dir8)
            if visited_key in visited and visited[visited_key] <= priority: continue
            visited[visited_key] = priority
            for next_dir8 in range(8):
                next_r, next_c = r + DR8[next_dir8], c + DC8[next_dir8]
                if not (0 <= next_r < GRID_SIZE and 0 <= next_c < GRID_SIZE): continue
                move_ok = False
                if next_dir8 % 2 == 0: move_ok = not self.has_wall(r, c, next_dir8 // 2)
                else: move_ok = self._can_move_diag(r, c, next_dir8)
                if move_ok:
                    move_cost = MOVE_COST[next_dir8]
                    new_dist = dist + move_cost
                    turn_inc = 1 if arr_dir8 is not None and next_dir8 != arr_dir8 else 0
                    new_turns = turns + turn_inc
                    new_priority = new_dist + turn_weight * float(new_turns)
                    next_visited_key = (next_r, next_c, next_dir8)
                    if next_visited_key not in visited or new_priority < visited[next_visited_key]:
                        new_path = path + [(next_r, next_c)]
                        heapq.heappush(pq, (new_priority, new_dist, new_turns, next_r, next_c, next_dir8, new_path))
        return [], "Unreachable"

    # --- Maze Generation ---
    def _get_neighbours(self, r, c, visited):
        neighbours = []
        for direction4 in range(4):
            nr, nc = r + DR4[direction4], c + DC4[direction4]
            if 0 <= nr < GRID_SIZE and 0 <= nc < GRID_SIZE and not visited[nr][nc]:
                neighbours.append(((nr, nc), direction4))
        return neighbours
    def _remove_wall(self, r, c, direction4):
        nr, nc = r + DR4[direction4], c + DC4[direction4]
        if direction4 == N4:
            if 0 <= c < GRID_SIZE: self.h_walls[r][c] = False
        elif direction4 == E4:
             if 0 <= r < GRID_SIZE: self.v_walls[r][c+1] = False
        elif direction4 == S4:
             if 0 <= c < GRID_SIZE: self.h_walls[r+1][c] = False
        elif direction4 == W4:
             if 0 <= r < GRID_SIZE: self.v_walls[r][c] = False

    def _recursive_backtracker_generate(self):
        visited = [[False for _ in range(GRID_SIZE)] for _ in range(GRID_SIZE)]
        stack = []
        start_r, start_c = self.start_cell
        visited[start_r][start_c] = True
        first_move_r, first_move_c = start_r + DR4[N4], start_c + DC4[N4]
        if 0 <= first_move_r < GRID_SIZE and 0 <= first_move_c < GRID_SIZE:
             self._remove_wall(start_r, start_c, N4)
             visited[first_move_r][first_move_c] = True
             stack.append((first_move_r, first_move_c))
             stack.append((start_r, start_c))
        else:
             stack.append((start_r, start_c))
        while stack:
            r, c = stack[-1]
            neighbours = self._get_neighbours(r, c, visited)
            if neighbours:
                (nr, nc), direction = random.choice(neighbours)
                self._remove_wall(r, c, direction)
                visited[nr][nc] = True
                stack.append((nr, nc))
            else:
                stack.pop()

    def _add_loops(self, probability):
        for r in range(1, GRID_SIZE):
            for c in range(GRID_SIZE):
                if self.h_walls[r][c] and random.random() < probability:
                    self.h_walls[r][c] = False
        for r in range(GRID_SIZE):
            for c in range(1, GRID_SIZE):
                 if self.v_walls[r][c] and random.random() < probability:
                     self.v_walls[r][c] = False

    def _is_true_center_post(self, r, c):
        center_r = GRID_SIZE // 2; center_c = GRID_SIZE // 2
        return r == center_r and c == center_c

    def add_wall_safe(self, wall_type, r, c):
        center_r, center_c = GRID_SIZE // 2, GRID_SIZE // 2
        try:
            if wall_type == 'h': # Connects post (r, c) and (r, c+1)
                if (r == center_r and c == center_c) or (r == center_r and c+1 == center_c): return
                if 0 <= r < len(self.h_walls) and 0 <= c < len(self.h_walls[0]): self.h_walls[r][c] = True
            elif wall_type == 'v': # Connects post (r, c) and (r+1, c)
                if (r == center_r and c == center_c) or (r+1 == center_r and c == center_c): return
                if 0 <= r < len(self.v_walls) and 0 <= c < len(self.v_walls[0]): self.v_walls[r][c] = True
        except IndexError: pass

    def remove_walls_around_post(self, r_post, c_post):
        try:
            if c_post > 0 and r_post < len(self.h_walls): self.h_walls[r_post][c_post-1] = False
            if c_post < GRID_SIZE and r_post < len(self.h_walls): self.h_walls[r_post][c_post] = False
            if r_post > 0 and c_post < len(self.v_walls[0]): self.v_walls[r_post-1][c_post] = False
            if r_post < GRID_SIZE and c_post < len(self.v_walls[0]): self.v_walls[r_post][c_post] = False
        except IndexError: pass

    def _ensure_post_connectivity(self):
        center_r, center_c = GRID_SIZE // 2, GRID_SIZE // 2
        for r in range(1, GRID_SIZE):
            for c in range(1, GRID_SIZE):
                if r == center_r and c == center_c: continue
                connected_walls = 0; possible_walls_to_add = []
                if c > 0:
                    if self.h_walls[r][c-1]: connected_walls += 1
                    else: possible_walls_to_add.append(('h', r, c-1))
                if c < GRID_SIZE:
                    if self.h_walls[r][c]: connected_walls += 1
                    else: possible_walls_to_add.append(('h', r, c))
                if r > 0:
                    if self.v_walls[r-1][c]: connected_walls += 1
                    else: possible_walls_to_add.append(('v', r-1, c))
                if r < GRID_SIZE:
                    if self.v_walls[r][c]: connected_walls += 1
                    else: possible_walls_to_add.append(('v', r, c))
                if connected_walls == 0 and possible_walls_to_add:
                    wall_type, wr, wc = random.choice(possible_walls_to_add)
                    self.add_wall_safe(wall_type, wr, wc)

    def _is_reachable(self, target_r, target_c):
        q = deque([self.start_cell]); visited = {self.start_cell}
        while q:
            r, c = q.popleft()
            if r == target_r and c == target_c: return True
            for dir4 in range(4):
                if not self.has_wall(r, c, dir4):
                    nr, nc = r + DR4[dir4], c + DC4[dir4]
                    if (0 <= nr < GRID_SIZE and 0 <= nc < GRID_SIZE and (nr, nc) not in visited):
                        visited.add((nr, nc)); q.append((nr, nc))
        return False

    def _ensure_single_goal_entry(self):
        R_start = GRID_SIZE // 2 - 1; C_start = GRID_SIZE // 2 - 1
        center_r, center_c = GRID_SIZE // 2, GRID_SIZE // 2
        local_goal_cells = {(R_start, C_start), (R_start, C_start + 1), (R_start + 1, C_start), (R_start + 1, C_start + 1)}
        perimeter_walls_defs = [
            ('h', R_start, C_start), ('h', R_start, C_start+1),('h', R_start+2, C_start), ('h', R_start+2, C_start+1),
            ('v', R_start, C_start), ('v', R_start+1, C_start),('v', R_start, C_start+2), ('v', R_start+1, C_start+2)]
        for p_type, p_r, p_c in perimeter_walls_defs: self.add_wall_safe(p_type, p_r, p_c)
        adjacent_candidates = []
        for gr, gc in local_goal_cells:
            for dir4 in range(4):
                 adj_r, adj_c = gr + DR4[dir4], gc + DC4[dir4]
                 if (0 <= adj_r < GRID_SIZE and 0 <= adj_c < GRID_SIZE and (adj_r, adj_c) not in local_goal_cells):
                     wall_info = None
                     if dir4 == N4: wall_info = ('h', gr, gc)
                     elif dir4 == E4: wall_info = ('v', gr, gc + 1)
                     elif dir4 == S4: wall_info = ('h', gr + 1, gc)
                     elif dir4 == W4: wall_info = ('v', gr, gc)
                     if wall_info:
                          candidate = (adj_r, adj_c, wall_info[0], wall_info[1], wall_info[2])
                          if candidate not in adjacent_candidates: adjacent_candidates.append(candidate)
        reachable_adjacent = []
        for adj_r, adj_c, wt, wr, wc in adjacent_candidates:
            if self._is_reachable(adj_r, adj_c): reachable_adjacent.append((adj_r, adj_c, wt, wr, wc))
        if reachable_adjacent:
            _, _, chosen_wt, chosen_wr, chosen_wc = random.choice(reachable_adjacent)
            try:
                if chosen_wt == 'h':
                    if 0 <= chosen_wr < len(self.h_walls) and 0 <= chosen_wc < len(self.h_walls[0]): self.h_walls[chosen_wr][chosen_wc] = False
                elif chosen_wt == 'v':
                     if 0 <= chosen_wr < len(self.v_walls) and 0 <= chosen_wc < len(self.v_walls[0]): self.v_walls[chosen_wr][chosen_wc] = False
            except IndexError: print(f"Warning: Failed to remove chosen goal entry wall: {chosen_wt, chosen_wr, chosen_wc}")
        else:
            print("WARNING: No reachable cells found adjacent to goal! Using fallback.")
            if perimeter_walls_defs:
                p_type, p_r, p_c = random.choice(perimeter_walls_defs)
                try:
                    if p_type == 'h': self.h_walls[p_r][p_c] = False
                    elif p_type == 'v': self.v_walls[p_r][p_c] = False
                except IndexError: pass
        self.remove_walls_around_post(center_r, center_c)

    def generate_maze(self):
        generation_attempts = 0; max_attempts = 100
        while True:
            generation_attempts += 1
            if generation_attempts > max_attempts:
                 messagebox.showerror("Generation Error", f"Failed to generate maze with path after {max_attempts} attempts.")
                 self.update_status("Maze generation failed."); return
            self.update_status(f"Generating maze (Attempt {generation_attempts})..."); self.master.update()
            self._initialize_all_walls()
            self._recursive_backtracker_generate()
            self._add_loops(MAZE_GENERATION_LOOP_PROBABILITY)
            self._ensure_post_connectivity()
            self._ensure_single_goal_entry()
            start_r, start_c = self.start_cell
            if 0 <= start_r < GRID_SIZE and 0 <= start_c + 1 <= GRID_SIZE:
                self.v_walls[start_r][start_c + 1] = True
            path_check, msg_check = self._calculate_dijkstra_path(TURN_PENALTY_SHORTEST)
            if path_check:
                self.find_and_draw_routes()
                self.update_status("Maze generated.")
                break
            else: pass

    # --- Save/Load ---
    def save_maze(self):
        filename = filedialog.asksaveasfilename(defaultextension=".json", filetypes=[("JSON files","*.json"),("All files","*.*")], title="Save Maze As")
        if not filename: return
        maze_data = {"grid_size": GRID_SIZE, "h_walls": self.h_walls, "v_walls": self.v_walls}
        try:
            with open(filename, 'w') as f: json.dump(maze_data, f, indent=2)
            self.update_status(f"Maze saved to {filename}")
        except Exception as e: messagebox.showerror("Save Error",f"Failed to save maze:\n{e}"); self.update_status("Save failed.")
    def load_maze(self):
        filename = filedialog.askopenfilename(filetypes=[("JSON files","*.json"),("All files","*.*")], title="Load Maze File")
        if not filename: return
        try:
            with open(filename, 'r') as f: maze_data = json.load(f)
            if not isinstance(maze_data, dict) or maze_data.get("grid_size") != GRID_SIZE: raise ValueError("Invalid format or size")
            self.h_walls = [[bool(w) for w in r] for r in maze_data['h_walls']]
            self.v_walls = [[bool(w) for w in r] for r in maze_data['v_walls']]
            self.initialize_outer_walls()
            # Visibility toggles NOT reset
            self.handle_resize(self.master.winfo_width(), self.master.winfo_height())
            self.update_status(f"Maze loaded from {filename}.")
        except Exception as e: messagebox.showerror("Load Error",f"Failed to load maze:\n{e}"); self.update_status(f"Load failed: {e}")

    def update_status(self, message):
        self.status_label.config(text=message)

# --- Main Execution ---
if __name__ == "__main__":
    root = tk.Tk()
    app = MazeEditor(root)
    root.mainloop()