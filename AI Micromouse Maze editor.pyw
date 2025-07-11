import tkinter as tk
from tkinter import (Canvas, Frame, Button, Label, Entry, messagebox, filedialog,
                     StringVar, DoubleVar, Listbox, Scrollbar, Toplevel, END, SINGLE)
import math
import json
import random # For generation
from collections import deque
import heapq
import time
import requests # For downloading
import os       # For folder creation and path manipulation

# Import numpy and scipy for smoothing
import numpy as np
try:
    from scipy.interpolate import splprep, splev
    SCIPY_AVAILABLE = True
except ImportError:
    SCIPY_AVAILABLE = False
    # Warning will be printed later and shown in a messagebox if needed

# --- Configuration Constants ---
DEFAULT_GRID_SIZE = 16 # Default size for new mazes
DEFAULT_CELL_VISUAL_SIZE_PX = 25 # Base size for scaling smoothing
MARGIN = 25
ROUTE_WIDTH = 2
MAZE_GENERATION_LOOP_PROBABILITY = 0.15
DOWNLOAD_FOLDER = "downloaded_mazes"
BASE_SMOOTHING_FACTOR = 1500 # Base smoothing factor at default cell size

# Physical dimensions for scaling
CELL_PHYSICAL_SIZE_M = 0.180      # 180 mm per cell
WALL_PHYSICAL_THICKNESS_M = 0.012 # 12 mm for wall thickness
POST_PHYSICAL_SIZE_M = 0.014      # 14 mm for post side length

# Colors
COLOR_BACKGROUND = "white"; COLOR_POST = "black"; COLOR_WALL = "blue"
COLOR_WALL_SEEN = "red"
COLOR_START = "lightgreen"; COLOR_GOAL = "lightblue"; COLOR_GRID_LINE = "#eee"
COLOR_ROUTE_LEFT = "gray"; COLOR_ROUTE_SHORTEST = "purple"
COLOR_ROUTE_STRAIGHTEST = "darkorange"; COLOR_ROUTE_DIAGONAL = "forest green"
COLOR_ROUTE_SMOOTHED = "cyan"
COLOR_KEY_SWATCH_BORDER = "#555"
COLOR_HIGHLIGHT_OPEN = "yellow"

# Turn Penalties
DEFAULT_TURN_WEIGHT_STRAIGHTEST = 4.0
TURN_PENALTY_SHORTEST = 0.01
TURN_PENALTY_DIAGONAL = 1.0

# --- Directions ---
N, NE, E, SE, S, SW, W, NW = 0, 1, 2, 3, 4, 5, 6, 7
DR8 = [-1,-1, 0, 1, 1, 1, 0,-1]; DC8 = [ 0, 1, 1, 1, 0,-1,-1,-1]
SQRT2 = math.sqrt(2.0)
MOVE_COST = [1.0, SQRT2, 1.0, SQRT2, 1.0, SQRT2, 1.0, SQRT2]
N4, E4, S4, W4 = 0, 1, 2, 3
DR4 = [-1, 0, 1, 0]; DC4 = [0, 1, 0, -1]

class MazeEditor:
    def __init__(self, master, initial_size=DEFAULT_GRID_SIZE):
        self.master = master
        # Title set in _set_grid_size

        self.grid_size = 0 # Will be set by _set_grid_size
        self.h_walls = []
        self.v_walls = []
        self.goal_cells = set()
        self.start_cell = (0, 0)
        self.start_pos_lh = (0, 0, N4)
        self._default_goal_cells = set() # Store the calculated default goal

        self.cell_visual_size_px = DEFAULT_CELL_VISUAL_SIZE_PX # Initial guess
        self.last_width = 0; self.last_height = 0
        self.resize_timer = None
        self.current_maze_file = None
        self.maze_modified = False

        # Route Data
        self.route_path_left = []; self.route_path_shortest = []
        self.route_path_straightest = []; self.route_path_diagonal = []
        self.straightest_path_pixel_vertices = [] # Stores (x,y) vertices of the straightest path
        self.msg_left=""; self.msg_shortest=""; self.msg_straightest=""; self.msg_diagonal=""; self.msg_smoothed=""

        self.turn_weight_var = DoubleVar(value=DEFAULT_TURN_WEIGHT_STRAIGHTEST)
        self.turn_weight_var.trace_add("write", self.on_config_change)

        # Route Visibility Toggles
        self.show_route_left_var = tk.BooleanVar(value=True)
        self.show_route_shortest_var = tk.BooleanVar(value=True)
        self.show_route_straightest_var = tk.BooleanVar(value=True) # Orange line
        self.show_route_diagonal_var = tk.BooleanVar(value=False)
        self.show_route_smoothed_var = tk.BooleanVar(value=True) # Cyan line
        self.highlight_open_cells_var = tk.BooleanVar(value=False)
        self.show_flood_fill_var = tk.BooleanVar(value=False)

        self.selected_size_var = tk.StringVar(value=str(initial_size))
        self.selected_size_var.trace_add("write", self.on_size_select_change)


        # --- Variables for Download Dialog state ---
        self.preview_canvas = None
        self.preview_after_id = None
        self.selected_maze_url = None

        # --- Mouse Simulation State ---
        self.mouse_sim_running = False
        self.sim_paused = False
        self.sim_history = []
        self.sim_history_index = -1
        self.show_sim_results = False
        self.mouse_sim_phase = None # "EXPLORE", "RETURN_TO_START", "SPEED_RUN"
        self.mouse_r, self.mouse_c = 0, 0
        self.mouse_dir4 = N4 # Default starting direction
        self.mouse_seen_h_walls = []
        self.mouse_seen_v_walls = []
        self.mouse_trail = [] # List of (r,c) cells visited in current run
        self.mouse_after_id = None # For scheduling next step
        self.mouse_walls_seen_count = 0
        self.mouse_run_count = 0


        # --- GUI Setup Order Change ---
        self._setup_gui()           # Create frames, canvas, status bar, **key_frame**
        self._create_color_key()    # Create the labels within key_frame -> self.key_label_xxx exist now
        # --- End Order Change ---

        # Set initial logical size and reset data structures
        self._set_grid_size(initial_size, is_initial=True)

        # Bindings
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<Shift-Button-1>", self.on_goal_set_click)
        self.canvas.bind("<Control-Button-1>", self.on_start_set_click)
        self.master.bind("<Configure>", self.schedule_resize)
        self.master.protocol("WM_DELETE_WINDOW", self.on_close_window)

        # Update GUI layout *before* scheduling the initial resize/draw
        self.master.update_idletasks()

        # --- Schedule the initial resize/draw slightly after mainloop starts ---
        self.master.after(10, lambda: self.handle_resize(self.master.winfo_width(), self.master.winfo_height()))

    @property
    def scaled_wall_thickness(self):
        """Calculates wall thickness in pixels based on physical size ratio."""
        if self.cell_visual_size_px <= 0: return 1
        ratio = WALL_PHYSICAL_THICKNESS_M / CELL_PHYSICAL_SIZE_M
        return max(1, self.cell_visual_size_px * ratio)

    @property
    def scaled_post_size(self):
        """Calculates post side length in pixels based on physical size ratio."""
        if self.cell_visual_size_px <= 0: return 2
        ratio = POST_PHYSICAL_SIZE_M / CELL_PHYSICAL_SIZE_M
        return max(2, self.cell_visual_size_px * ratio)


    # --- Callbacks ---
    def on_config_change(self, *args):
        """Callback for changes in Turn Weight."""
        try:
            current_turn_weight = self.turn_weight_var.get()
            if current_turn_weight < 0: self.turn_weight_var.set(0.0)
            self.find_and_draw_routes() # Recalculate routes and redraw
            self.update_status("Turn weight changed, view updated.")
        except tk.TclError: pass
        except ValueError: pass

    def on_size_select_change(self, *args):
        """Callback when the size radio button selection changes."""
        # Check for unsaved changes *before* changing anything
        if not self._check_save_before_action("changing grid size"):
            # Revert radio button if user cancelled save/change
            self.selected_size_var.set(str(self.grid_size))
            return

        try:
            new_size = int(self.selected_size_var.get())
            if new_size != self.grid_size:
                 if self._set_grid_size(new_size): # Try to set the logical size
                      self.master.update_idletasks() # Ensure window is updated
                      self.handle_resize(self.master.winfo_width(), self.master.winfo_height())
                 else:
                      # If _set_grid_size failed (e.g., invalid value somehow), revert button
                      self.selected_size_var.set(str(self.grid_size))

        except ValueError:
            messagebox.showerror("Error", "Invalid size selection value.")
            self.selected_size_var.set(str(self.grid_size)) # Revert radio button


    def on_goal_set_click(self, event):
        """Handles Shift+Click to toggle goal cells."""
        r, c = self.pixel_to_cell(event.x, event.y)
        if not (0 <= r < self.grid_size and 0 <= c < self.grid_size): return
        if (r, c) == self.start_cell:
            self.update_status("Cannot set start cell as goal."); return
        cell = (r, c)
        modified = False
        if cell in self.goal_cells:
            if len(self.goal_cells) > 1:
                self.goal_cells.remove(cell); self.update_status(f"Goal cell removed: ({r},{c})"); modified = True
            else: self.update_status("Cannot remove the last goal cell.")
        else:
            self.goal_cells.add(cell); self.update_status(f"Goal cell added: ({r},{c})"); modified = True
        if modified:
            self.show_sim_results = False # Old sim results are now invalid
            self.maze_modified = True; self._update_window_title(); self.find_and_draw_routes()

    def on_start_set_click(self, event):
        """Handles Control+Click to move the start cell."""
        r, c = self.pixel_to_cell(event.x, event.y)

        # Validate click is inside grid
        if not (0 <= r < self.grid_size and 0 <= c < self.grid_size):
            return
        # Do nothing if clicking the same cell
        if (r, c) == self.start_cell:
            return
        # Prevent setting start on a goal cell
        if (r, c) in self.goal_cells:
            self.update_status("Cannot set start on a goal cell.")
            return

        # Update the start cell
        self.start_cell = (r, c)
        self.start_pos_lh = (r, c, N4) # Default new start to face North

        # Update maze state
        self.maze_modified = True
        self.show_sim_results = False # Old simulation results are now invalid

        # Update GUI and recalculate everything
        self.update_status(f"Start cell moved to ({r}, {c}).")
        self._update_window_title()
        self.find_and_draw_routes()


    # --- Core Logic ---
    def _set_grid_size(self, new_size, is_initial=False):
        """Sets the grid size and reinitializes dependent structures."""
        if new_size not in [16, 32]:
            if not is_initial: messagebox.showerror("Error", f"Unsupported grid size: {new_size}. Must be 16 or 32.")
            if self.grid_size not in [16, 32]: self.grid_size = DEFAULT_GRID_SIZE
            self.selected_size_var.set(str(self.grid_size)); return False

        if not is_initial and self.grid_size == new_size: return True # No change needed

        self.show_sim_results = False
        self.grid_size = new_size
        self.selected_size_var.set(str(new_size))

        # Recalculate start/goal defaults
        self.start_cell = (self.grid_size - 1, 0)
        self.start_pos_lh = (self.grid_size - 1, 0, N4)
        center_r1 = self.grid_size // 2 - 1; center_c1 = self.grid_size // 2 - 1
        self._default_goal_cells = {(r,c) for r in range(center_r1, center_r1+2) for c in range(center_c1, center_c1+2)}
        if not is_initial or not self.goal_cells: # Reset goal if not initial setup or if goal was empty
             self.goal_cells = self._default_goal_cells.copy()

        # Reinitialize wall arrays
        self.h_walls = [[False for _ in range(self.grid_size)] for _ in range(self.grid_size + 1)]
        self.v_walls = [[False for _ in range(self.grid_size + 1)] for _ in range(self.grid_size)]
        self.initialize_outer_walls()

        self.clear_routes()
        if not is_initial:
            self.maze_modified = False
            self.current_maze_file = None

        self._update_window_title()

        # Reset maze walls, always skip redraw as drawing is handled elsewhere
        self.reset_maze(add_start_wall=True, called_from_set_size=True, skip_redraw=True)

        return True

    @property
    def click_tolerance(self): return self.cell_visual_size_px * 0.4

    def _setup_gui(self):
        """Creates the main GUI elements."""
        self.master.rowconfigure(1, weight=1); self.master.columnconfigure(0, weight=1)
        top_control_frame = Frame(self.master); top_control_frame.grid(row=0, column=0, sticky="ew", pady=(10, 0), padx=10)
        left_ctrl_frame = Frame(top_control_frame); left_ctrl_frame.pack(side=tk.LEFT)
        size_frame = Frame(left_ctrl_frame, bd=1, relief=tk.GROOVE); size_frame.pack(side=tk.LEFT, padx=5, pady=2)
        Label(size_frame, text="Size:").pack(side=tk.LEFT, padx=(5, 0))
        tk.Radiobutton(size_frame, text="16x16", variable=self.selected_size_var, value="16").pack(side=tk.LEFT)
        tk.Radiobutton(size_frame, text="32x32", variable=self.selected_size_var, value="32").pack(side=tk.LEFT, padx=(0, 5))
        Button(left_ctrl_frame, text="Reset Maze", command=self.reset_maze).pack(side=tk.LEFT, padx=5)
        Button(left_ctrl_frame, text="Generate Maze", command=self.generate_maze).pack(side=tk.LEFT, padx=5)
        Button(left_ctrl_frame, text="Save Maze", command=self.save_maze_text).pack(side=tk.LEFT, padx=5)
        Button(left_ctrl_frame, text="Load Maze", command=self.load_maze_text).pack(side=tk.LEFT, padx=5)
        Button(left_ctrl_frame, text="Load from GitHub", command=self.fetch_github_maze_list).pack(side=tk.LEFT, padx=5)

        # --- Simulation Controls ---
        # This button is swapped out for the control frame during simulation
        self.simulate_button = Button(left_ctrl_frame, text="Simulate Mouse", command=self.start_mouse_simulation)
        self.simulate_button.pack(side=tk.LEFT, padx=10)

        # The frame for interactive simulation controls (initially hidden)
        self.sim_controls_frame = Frame(left_ctrl_frame)

        self.sim_stop_button = Button(self.sim_controls_frame, text="Stop", command=self.stop_mouse_simulation)
        self.sim_stop_button.pack(side=tk.LEFT, padx=(10, 0))

        self.sim_back_button = Button(self.sim_controls_frame, text="⏪", command=self._sim_step_backward)
        self.sim_back_button.pack(side=tk.LEFT, padx=(5,0))

        self.sim_pause_button = Button(self.sim_controls_frame, text="⏸", command=self._toggle_sim_pause)
        self.sim_pause_button.pack(side=tk.LEFT)

        self.sim_forward_button = Button(self.sim_controls_frame, text="⏩", command=self._sim_step_forward)
        self.sim_forward_button.pack(side=tk.LEFT)
        # --- End Simulation Controls ---

        right_controls_frame = Frame(top_control_frame); right_controls_frame.pack(side=tk.RIGHT, padx=10)

        weight_frame = Frame(right_controls_frame); weight_frame.pack(side=tk.LEFT, padx=5)
        Label(weight_frame, text="Turn W:").pack(side=tk.LEFT)
        vcmd_turn = (self.master.register(self.validate_float_entry), '%P')
        self.turn_weight_entry = Entry(weight_frame, textvariable=self.turn_weight_var, width=5, validate='key', validatecommand=vcmd_turn)
        self.turn_weight_entry.pack(side=tk.LEFT, padx=(2, 0))

        view_options_frame = Frame(right_controls_frame); view_options_frame.pack(side=tk.LEFT, padx=5)
        self.highlight_checkbutton = tk.Checkbutton(view_options_frame, text="Highlight Open", variable=self.highlight_open_cells_var, command=self.find_and_draw_routes)
        self.highlight_checkbutton.pack(side=tk.TOP, anchor='w')
        self.show_weights_checkbutton = tk.Checkbutton(view_options_frame, text="Show Weights", variable=self.show_flood_fill_var, command=self.find_and_draw_routes)
        self.show_weights_checkbutton.pack(side=tk.TOP, anchor='w')

        initial_canvas_width = 2*MARGIN+DEFAULT_GRID_SIZE*DEFAULT_CELL_VISUAL_SIZE_PX
        initial_canvas_height = 2*MARGIN+DEFAULT_GRID_SIZE*DEFAULT_CELL_VISUAL_SIZE_PX
        self.canvas = Canvas(self.master, width=initial_canvas_width, height=initial_canvas_height, bg=COLOR_BACKGROUND)
        self.canvas.grid(row=1, column=0, sticky="nsew", pady=(5, 5), padx=10)
        self.key_frame = Frame(self.master, bd=1, relief=tk.GROOVE); self.key_frame.grid(row=2, column=0, sticky="ew", pady=(0, 5), padx=10)
        self.status_label = Label(self.master, text="Initializing...", bd=1, relief=tk.SUNKEN, anchor=tk.W); self.status_label.grid(row=3, column=0, sticky="ew", ipady=2)

    def _create_color_key(self):
        """Creates the 5 elements within the color key frame."""
        for widget in self.key_frame.winfo_children(): widget.destroy()
        self.key_frame.columnconfigure(0, weight=1); self.key_frame.columnconfigure(1, weight=1); self.key_frame.columnconfigure(2, weight=2); self.key_frame.columnconfigure(3, weight=1); self.key_frame.columnconfigure(4, weight=1)
        font_size = 8
        def create_key_entry(parent, col, color, var):
            frame = Frame(parent); frame.grid(row=0, column=col, sticky='w', padx=3, pady=0)
            toggle = tk.Checkbutton(frame, variable=var, command=self.draw_current_routes, pady=0, padx=0); toggle.pack(side=tk.LEFT)
            Label(frame, text="", width=2, relief=tk.RAISED, bd=1, bg=color).pack(side=tk.LEFT, padx=(0,2))
            label_widget = Label(frame, text="--", anchor='w', font=("TkDefaultFont", font_size)); label_widget.pack(side=tk.LEFT, fill='x', expand=True)
            return label_widget
        self.key_label_left = create_key_entry(self.key_frame, 0, COLOR_ROUTE_LEFT, self.show_route_left_var)
        self.key_label_shortest = create_key_entry(self.key_frame, 1, COLOR_ROUTE_SHORTEST, self.show_route_shortest_var)
        self.key_label_straightest = create_key_entry(self.key_frame, 2, COLOR_ROUTE_STRAIGHTEST, self.show_route_straightest_var)
        self.key_label_diagonal = create_key_entry(self.key_frame, 3, COLOR_ROUTE_DIAGONAL, self.show_route_diagonal_var)
        self.key_label_smoothed = create_key_entry(self.key_frame, 4, COLOR_ROUTE_SMOOTHED, self.show_route_smoothed_var)

    def validate_float_entry(self, P):
        """Validation function for float Entry widgets."""
        if P == "" or P == "." or P == "-": return True
        if P.startswith("-") and P.count('-') > 1: return False
        if P.startswith("-") and P == "-.": return True
        try:
            parts = P.split('.')
            if len(parts) > 2: return False
            if not parts[0].lstrip('-').isdigit() and parts[0].lstrip('-') != "": return False
            if len(parts) > 1 and not parts[1].isdigit() and parts[1] != "": return False
            return True
        except Exception: return False

    def _update_window_title(self):
        """Updates the window title based on grid size, current file, modified state."""
        base_title = f"Micromouse Maze Editor ({self.grid_size}x{self.grid_size})"
        title = base_title
        if self.current_maze_file:
            filename = os.path.basename(self.current_maze_file) if not self.current_maze_file.startswith("GitHub:") else self.current_maze_file.split("GitHub: ", 1)[1]
            title = f"{base_title} - {filename}"
        if self.maze_modified: title += " *"
        self.master.title(title)

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
        if not self.grid_size: return
        try:
             canvas_width = self.canvas.winfo_width(); canvas_height = self.canvas.winfo_height()
             if canvas_width <= 1 or canvas_height <= 1:
                  self.master.after(50, lambda: self.handle_resize(self.master.winfo_width(), self.master.winfo_height()))
                  return
        except Exception:
             estimated_control_height = 100
             canvas_width = width - 2 * MARGIN; canvas_height = height - estimated_control_height
             if canvas_width <= 0 or canvas_height <= 0: return
        cell_size_w = (canvas_width - 2 * MARGIN) / self.grid_size
        cell_size_h = (canvas_height - 2 * MARGIN) / self.grid_size
        new_cell_size = max(5, int(min(cell_size_w, cell_size_h)))
        if new_cell_size != self.cell_visual_size_px:
            self.cell_visual_size_px = new_cell_size
            self.find_and_draw_routes()
        elif not self.canvas.find_all(): self.find_and_draw_routes()

    def initialize_outer_walls(self):
        gs = self.grid_size
        if not self.h_walls or not self.v_walls or len(self.h_walls) < gs + 1 or len(self.v_walls) < gs: return
        for c in range(gs): self.h_walls[0][c] = self.h_walls[gs][c] = True
        for r in range(gs): self.v_walls[r][0] = self.v_walls[r][gs] = True

    def _check_save_before_action(self, action_description="continue"):
        if not self.maze_modified: return True
        response = messagebox.askyesnocancel("Unsaved Changes", f"Maze has been modified. Save changes before {action_description}?", parent=self.master)
        if response is True: return self.save_maze_text()
        elif response is False: return True
        else: return False

    def reset_maze(self, add_start_wall=True, called_from_set_size=False, skip_redraw=False):
        if not called_from_set_size:
             if not self._check_save_before_action("resetting"): return
        target_size = self.grid_size
        try:
            if not called_from_set_size:
                 target_size = int(self.selected_size_var.get())
                 if target_size not in [16, 32]: target_size = self.grid_size
        except ValueError: pass
        if not called_from_set_size and self.grid_size != target_size:
            self._set_grid_size(target_size); return

        self.show_sim_results = False
        gs = self.grid_size
        for r in range(1, gs):
            for c in range(gs): self.h_walls[r][c] = False
        for r in range(gs):
            for c in range(1, gs): self.v_walls[r][c] = False
        if not called_from_set_size or not self.goal_cells:
            center_r1 = gs // 2 - 1; center_c1 = gs // 2 - 1
            self._default_goal_cells = {(r,c) for r in range(center_r1, center_r1+2) for c in range(center_c1, center_c1+2)}
            self.goal_cells = self._default_goal_cells.copy()
        if add_start_wall:
            try:
                start_r, start_c = self.start_cell
                if start_c + 1 <= gs: self.v_walls[start_r][start_c + 1] = True
            except IndexError: print("Warning: Could not add default start wall (index error).")
        if not called_from_set_size:
            self.current_maze_file = None; self.maze_modified = False
            self._update_window_title()
        if not skip_redraw: self.find_and_draw_routes()
        self.update_status(f"Maze reset to empty {gs}x{gs}.")

    def _initialize_all_walls(self):
        gs = self.grid_size
        for r in range(1, gs):
            for c in range(gs): self.h_walls[r][c] = True
        for r in range(gs):
            for c in range(1, gs): self.v_walls[r][c] = True

    def clear_routes(self):
        self.route_path_left = []; self.route_path_shortest = []
        self.route_path_straightest = []; self.route_path_diagonal = []
        self.straightest_path_pixel_vertices = []
        self.canvas.delete("route_left", "route_shortest", "route_straightest",
                           "route_diagonal", "route_smoothed", "mouse_trail", "mouse_sim_indicator")

    def cell_to_pixel(self, r, c):
        x = MARGIN + c * self.cell_visual_size_px; y = MARGIN + r * self.cell_visual_size_px; return x, y
    def cell_center_to_pixel(self, r, c, offset_x=0, offset_y=0):
        x = MARGIN + (c + 0.5) * self.cell_visual_size_px + offset_x; y = MARGIN + (r + 0.5) * self.cell_visual_size_px + offset_y; return x, y
    def wall_midpoint_to_pixel(self, r_cell, c_cell, direction4):
        cell_size = self.cell_visual_size_px; center_x, center_y = self.cell_center_to_pixel(r_cell, c_cell); half_cell = cell_size * 0.5
        if direction4 == N4:   y_mid = center_y - half_cell; x_mid = center_x
        elif direction4 == E4: x_mid = center_x + half_cell; y_mid = center_y
        elif direction4 == S4: y_mid = center_y + half_cell; x_mid = center_x
        elif direction4 == W4: x_mid = center_x - half_cell; y_mid = center_y
        else: return center_x, center_y
        return x_mid, y_mid
    def post_to_pixel(self, r_post, c_post):
        x = MARGIN + c_post * self.cell_visual_size_px; y = MARGIN + r_post * self.cell_visual_size_px; return x, y
    def pixel_to_cell(self, x, y):
        if self.cell_visual_size_px <= 0: return (-1,-1)
        x_adj = x - MARGIN; y_adj = y - MARGIN
        c = int(x_adj / self.cell_visual_size_px); r = int(y_adj / self.cell_visual_size_px)
        if 0 <= r < self.grid_size and 0 <= c < self.grid_size: return r, c
        else: return -1, -1

    def has_wall(self, r, c, direction4):
        gs = self.grid_size
        if not (0 <= r < gs and 0 <= c < gs): return True
        try:
            if direction4 == N4: return self.h_walls[r][c]
            elif direction4 == E4: return self.v_walls[r][c+1]
            elif direction4 == S4: return self.h_walls[r+1][c]
            elif direction4 == W4: return self.v_walls[r][c]
        except IndexError: return True
        return True
    def _can_move_diag(self, r, c, diag_direction):
        gs = self.grid_size
        if not (0 <= r < gs and 0 <= c < gs): return False
        if diag_direction == 1: return not self.has_wall(r, c, N4) and not self.has_wall(r, c, E4)
        elif diag_direction == 3: return not self.has_wall(r, c, S4) and not self.has_wall(r, c, E4)
        elif diag_direction == 5: return not self.has_wall(r, c, S4) and not self.has_wall(r, c, W4)
        elif diag_direction == 7: return not self.has_wall(r, c, N4) and not self.has_wall(r, c, W4)
        return False
    def get_wall_from_coords(self, click_x, click_y):
        min_dist_sq = (self.click_tolerance ** 2) + 1; closest_wall = None
        cell_size = self.cell_visual_size_px; gs = self.grid_size
        if cell_size <= 0: return None
        r_approx_cell, c_approx_cell = self.pixel_to_cell(click_x, click_y)
        if r_approx_cell < 0: return None
        for r_wall_check in range(max(0, r_approx_cell), min(gs + 1, r_approx_cell + 2)):
            for c_cell_check in range(max(0, c_approx_cell - 1), min(gs, c_approx_cell + 2)):
                if 0 < r_wall_check < gs:
                    wall_mid_x = MARGIN + (c_cell_check + 0.5) * cell_size; wall_mid_y = MARGIN + r_wall_check * cell_size
                    d2 = (click_x - wall_mid_x)**2 + (click_y - wall_mid_y)**2
                    if d2 < min_dist_sq: min_dist_sq = d2; closest_wall = ('h', r_wall_check, c_cell_check)
        for c_wall_check in range(max(0, c_approx_cell), min(gs + 1, c_approx_cell + 2)):
            for r_cell_check in range(max(0, r_approx_cell - 1), min(gs, r_approx_cell + 2)):
                if 0 < c_wall_check < gs:
                    wall_mid_x = MARGIN + c_wall_check * cell_size; wall_mid_y = MARGIN + (r_cell_check + 0.5) * cell_size
                    d2 = (click_x - wall_mid_x)**2 + (click_y - wall_mid_y)**2
                    if d2 < min_dist_sq: min_dist_sq = d2; closest_wall = ('v', r_cell_check, c_wall_check)
        if min_dist_sq <= (self.click_tolerance ** 2): return closest_wall
        return None
    def on_canvas_click(self, event):
        wall_info = self.get_wall_from_coords(event.x, event.y)
        if wall_info:
            self.show_sim_results = False
            wall_type, r, c = wall_info; toggled = False
            try:
                if wall_type == 'h': self.h_walls[r][c] = not self.h_walls[r][c]; toggled = True
                elif wall_type == 'v': self.v_walls[r][c] = not self.v_walls[r][c]; toggled = True
            except IndexError: pass
            if toggled:
                self.maze_modified = True; self.find_and_draw_routes()
                self.update_status(f"Wall {'H' if wall_type=='h' else 'V'}({r},{c}) toggled.")
                self._update_window_title()
    def on_close_window(self):
        if self.mouse_sim_running: self.mouse_sim_running = False
        if self._check_save_before_action("closing"): self.master.destroy()

    def draw_maze(self):
        cell_size = self.cell_visual_size_px
        gs = self.grid_size
        wall_thickness = self.scaled_wall_thickness
        post_size = self.scaled_post_size

        if cell_size <= 0 or not gs: return
        self.canvas.delete("all")
        start_r, start_c = self.start_cell
        highlight_on = self.highlight_open_cells_var.get()

        # Draw cells
        for r in range(gs):
            for c in range(gs):
                x0, y0 = self.cell_to_pixel(r, c)
                x1, y1 = x0 + cell_size, y0 + cell_size
                fill_color = COLOR_BACKGROUND
                if (r, c) == (start_r, start_c): fill_color = COLOR_START
                elif (r, c) in self.goal_cells: fill_color = COLOR_GOAL
                elif highlight_on:
                    if not self.has_wall(r, c, N4) and not self.has_wall(r, c, E4) and \
                       not self.has_wall(r, c, S4) and not self.has_wall(r, c, W4):
                        fill_color = COLOR_HIGHLIGHT_OPEN
                self.canvas.create_rectangle(x0, y0, x1, y1, fill=fill_color, outline=COLOR_GRID_LINE, tags="cell")

        if self.show_flood_fill_var.get() and self.goal_cells:
            turn_weight = self.turn_weight_var.get()
            cost_map = self._calculate_dijkstra_for_weights(turn_weight)
            for r in range(gs):
                for c in range(gs):
                    cost_val = cost_map[r][c]
                    if cost_val != float('inf'):
                        x_center, y_center = self.cell_center_to_pixel(r, c)
                        font_size = max(6, int(self.cell_visual_size_px / 3))
                        self.canvas.create_text(x_center, y_center, text=f"{cost_val:.0f}",
                                                font=("Arial", font_size), fill=COLOR_POST, tags="flood_fill_text")

        # Draw start arrow
        if start_r is not None and start_c is not None and start_r < gs:
            arrow_center_x, arrow_base_y = self.cell_center_to_pixel(start_r, start_c)
            arrow_tip_y = arrow_base_y - cell_size * 0.4
            arrow_width = max(1, int(cell_size * 0.15))
            self.canvas.create_line(arrow_center_x, arrow_base_y, arrow_center_x, arrow_tip_y, arrow=tk.LAST, fill="black", width=arrow_width, tags="start_arrow")

        # Draw walls
        for r_wall in range(gs + 1):
            for c_wall in range(gs):
                if r_wall < len(self.h_walls) and c_wall < len(self.h_walls[0]) and self.h_walls[r_wall][c_wall]:
                    x0, y0 = self.cell_to_pixel(r_wall, c_wall); x1 = x0 + cell_size; y1 = y0
                    wall_color = COLOR_WALL
                    if self.mouse_sim_running or self.show_sim_results:
                        try:
                            if self.mouse_seen_h_walls[r_wall][c_wall]: wall_color = COLOR_WALL_SEEN
                        except IndexError: pass
                    self.canvas.create_line(x0, y0, x1, y1, fill=wall_color, width=wall_thickness, tags="wall")

        for r_wall in range(gs):
            for c_wall in range(gs + 1):
                 if r_wall < len(self.v_walls) and c_wall < len(self.v_walls[0]) and self.v_walls[r_wall][c_wall]:
                    x0, y0 = self.cell_to_pixel(r_wall, c_wall); x1 = x0; y1 = y0 + cell_size
                    wall_color = COLOR_WALL
                    if self.mouse_sim_running or self.show_sim_results:
                        try:
                            if self.mouse_seen_v_walls[r_wall][c_wall]: wall_color = COLOR_WALL_SEEN
                        except IndexError: pass
                    self.canvas.create_line(x0, y0, x1, y1, fill=wall_color, width=wall_thickness, tags="wall")

        # Draw square posts
        for r_post in range(gs + 1):
            for c_post in range(gs + 1):
                x_center, y_center = self.post_to_pixel(r_post, c_post)
                half_post = post_size / 2
                self.canvas.create_rectangle(
                    x_center - half_post, y_center - half_post,
                    x_center + half_post, y_center + half_post,
                    fill=COLOR_POST, outline=COLOR_POST, tags="post"
                )


    def _calculate_path_distance(self, path):
        distance = 0.0
        if len(path) < 2: return 0.0
        for i in range(len(path) - 1):
            r1, c1 = path[i]; r2, c2 = path[i+1]; dr = abs(r1 - r2); dc = abs(c1 - c2)
            if dr + dc == 1: distance += CELL_PHYSICAL_SIZE_M
            elif dr == 1 and dc == 1: distance += CELL_PHYSICAL_SIZE_M * SQRT2
        return distance

    def find_and_draw_routes(self):
        if self.mouse_sim_running or self.sim_paused:
             self._draw_simulation_state()
             return

        if not self.goal_cells:
            self.clear_routes(); self.draw_maze()
            self.msg_left="No goal"; self.msg_shortest="No goal"; self.msg_straightest="No goal"; self.msg_diagonal="No goal"; self.msg_smoothed="No goal"
        else:
            path_left, msg_left_base = self._calculate_left_hand_path()
            path_shortest, msg_shortest_base = self._calculate_dijkstra_path(TURN_PENALTY_SHORTEST)
            current_turn_weight = self.turn_weight_var.get()
            path_straightest, msg_straightest_base = self._calculate_dijkstra_path(current_turn_weight)
            path_diagonal, msg_diagonal_base = self._calculate_dijkstra_diag_path(TURN_PENALTY_DIAGONAL)
            self.straightest_path_pixel_vertices = self._calculate_pixel_vertices(path_straightest)
            dist_left = self._calculate_path_distance(path_left); dist_shortest = self._calculate_path_distance(path_shortest)
            dist_straightest = self._calculate_path_distance(path_straightest); dist_diagonal = self._calculate_path_distance(path_diagonal)
            self.msg_left = f"{msg_left_base}, {dist_left:.2f}m" if path_left else msg_left_base
            self.msg_shortest = f"{msg_shortest_base}, {dist_shortest:.2f}m" if path_shortest else msg_shortest_base
            self.msg_straightest = f"{msg_straightest_base}, {dist_straightest:.2f}m" if path_straightest else msg_straightest_base
            self.msg_diagonal = f"{msg_diagonal_base}, {dist_diagonal:.2f}m" if path_diagonal else msg_diagonal_base
            can_smooth = SCIPY_AVAILABLE and len(self.straightest_path_pixel_vertices) >= 4
            self.msg_smoothed = "(Smoothed)" if can_smooth else ("(scipy missing)" if not SCIPY_AVAILABLE else ("(Base path short)" if self.straightest_path_pixel_vertices else "(No base path)"))
            self.route_path_left = path_left; self.route_path_shortest = path_shortest
            self.route_path_straightest = path_straightest; self.route_path_diagonal = path_diagonal

        self.draw_maze(); self.draw_current_routes()
        w_text = f"(w={self.turn_weight_var.get():.1f})"
        if hasattr(self, 'key_label_left'): self.key_label_left.config(text=f"L: {self.msg_left}")
        if hasattr(self, 'key_label_shortest'): self.key_label_shortest.config(text=f"S: {self.msg_shortest}")
        if hasattr(self, 'key_label_straightest'): self.key_label_straightest.config(text=f"St {w_text}: {self.msg_straightest}")
        if hasattr(self, 'key_label_diagonal'): self.key_label_diagonal.config(text=f"Diag: {self.msg_diagonal}")
        if hasattr(self, 'key_label_smoothed'): self.key_label_smoothed.config(text=f"Sm: {self.msg_smoothed}")


    def _calculate_pixel_vertices(self, path):
        if not path: return []
        vertices = []
        start_r, start_c = path[0]; start_x, start_y = self.cell_center_to_pixel(start_r, start_c)
        vertices.append((start_x, start_y)); last_x, last_y = start_x, start_y
        if len(path) >= 2:
            for i in range(1, len(path)):
                r0, c0 = path[i-1]; r1, c1 = path[i]
                dr = r1 - r0; dc = c1 - c0
                is_ortho = abs(dr) + abs(dc) == 1; is_diag = abs(dr) == 1 and abs(dc) == 1
                x2, y2 = last_x, last_y
                if is_ortho:
                    move_dir4 = -1
                    if dr == -1:    move_dir4 = N4
                    elif dr == 1:  move_dir4 = S4
                    elif dc == -1: move_dir4 = W4
                    elif dc == 1:  move_dir4 = E4
                    if move_dir4 != -1: entry_dir4 = (move_dir4 + 2) % 4; x2, y2 = self.wall_midpoint_to_pixel(r1, c1, entry_dir4)
                    else: x2, y2 = self.cell_center_to_pixel(r1, c1)
                elif is_diag: x2, y2 = self.cell_center_to_pixel(r1, c1)
                else: x2, y2 = self.cell_center_to_pixel(r1, c1)
                if not vertices or (abs(x2 - vertices[-1][0]) > 1e-6 or abs(y2 - vertices[-1][1]) > 1e-6): vertices.append((x2, y2))
                last_x, last_y = x2, y2
        final_r, final_c = path[-1]; final_x, final_y = self.cell_center_to_pixel(final_r, final_c)
        if not vertices or (abs(final_x - vertices[-1][0]) > 1e-6 or abs(final_y - vertices[-1][1]) > 1e-6): vertices.append((final_x, final_y))
        return vertices

    def _calculate_left_hand_path(self):
        gs = self.grid_size
        r, c, direction = self.start_pos_lh; path = [(r, c)]; visited_states = set([(r, c, direction)])
        max_steps = gs * gs * 5; step_count = 0; found_goal = False
        while step_count < max_steps:
            step_count += 1;
            if (r, c) in self.goal_cells: found_goal = True; break
            left_dir4 = (direction - 1 + 4) % 4; wall_left = self.has_wall(r, c, left_dir4)
            next_r, next_c, next_dir = r, c, direction
            if not wall_left: next_dir = left_dir4; next_r += DR4[next_dir]; next_c += DC4[next_dir]
            else:
                wall_ahead = self.has_wall(r, c, direction)
                if not wall_ahead: next_r += DR4[direction]; next_c += DC4[direction]
                else: next_dir = (direction + 1) % 4; next_r, next_c = r, c
            if not (0 <= next_r < gs and 0 <= next_c < gs): next_dir = (direction + 1) % 4; next_r, next_c = r, c
            r, c, direction = next_r, next_c, next_dir; current_state = (r, c, direction)
            if current_state in visited_states:
                 if (r, c) in self.goal_cells: found_goal = True
                 return path, f"Loop ({step_count} steps)"
            visited_states.add(current_state)
            if not path or path[-1] != (r,c): path.append((r, c))
        if found_goal: return path, f"Goal ({len(path) - 1} steps)"
        elif step_count >= max_steps: return path, f"Max steps ({max_steps})"
        else: return path, "Unreachable"

    def _calculate_dijkstra_path(self, turn_weight):
        gs = self.grid_size
        start_node = self.start_cell; pq = [(0.0, 0.0, 0, start_node[0], start_node[1], None, [start_node])]; visited = {}
        while pq:
            priority, cost, turns, r, c, arr_dir, path = heapq.heappop(pq)
            if (r, c) in self.goal_cells: return path, f"Goal ({cost:.0f}c, {turns}t)"
            visited_key = (r, c, arr_dir)
            if visited_key in visited and visited[visited_key] <= priority: continue
            visited[visited_key] = priority
            for next_dir4 in range(4):
                if not self.has_wall(r, c, next_dir4):
                    next_r, next_c = r + DR4[next_dir4], c + DC4[next_dir4]
                    if not (0 <= next_r < gs and 0 <= next_c < gs): continue
                    new_cost = cost + 1.0; turn_inc = 1 if arr_dir is not None and next_dir4 != arr_dir else 0
                    new_turns = turns + turn_inc; new_priority = new_cost + turn_weight * float(new_turns)
                    next_visited_key = (next_r, next_c, next_dir4)
                    if next_visited_key not in visited or new_priority < visited[next_visited_key]:
                        new_path = path + [(next_r, next_c)]; heapq.heappush(pq, (new_priority, new_cost, new_turns, next_r, next_c, next_dir4, new_path))
        return [], "Unreachable"

    def _calculate_dijkstra_diag_path(self, turn_weight):
        gs = self.grid_size
        start_node = self.start_cell; pq = [(0.0, 0.0, 0, start_node[0], start_node[1], None, [start_node])]; visited = {}
        while pq:
            priority, cost, turns, r, c, arr_dir8, path = heapq.heappop(pq)
            if (r, c) in self.goal_cells: return path, f"Goal ({cost:.1f} cost, {turns}t)"
            visited_key = (r, c, arr_dir8)
            if visited_key in visited and visited[visited_key] <= priority: continue
            visited[visited_key] = priority
            for next_dir8 in range(len(DR8)):
                next_r, next_c = r + DR8[next_dir8], c + DC8[next_dir8]
                if not (0 <= next_r < gs and 0 <= next_c < gs): continue
                move_ok = (next_dir8 % 2 == 0 and not self.has_wall(r, c, next_dir8 // 2)) or \
                          (next_dir8 % 2 != 0 and self._can_move_diag(r, c, next_dir8))
                if move_ok:
                    move_cost_val = MOVE_COST[next_dir8]; new_cost = cost + move_cost_val
                    turn_inc = 1 if arr_dir8 is not None and next_dir8 != arr_dir8 else 0
                    new_turns = turns + turn_inc; new_priority = new_cost + turn_weight * float(new_turns)
                    next_visited_key = (next_r, next_c, next_dir8)
                    if next_visited_key not in visited or new_priority < visited[next_visited_key]:
                        new_path = path + [(next_r, next_c)]; heapq.heappush(pq, (new_priority, new_cost, new_turns, next_r, next_c, next_dir8, new_path))
        return [], "Unreachable"

    def draw_current_routes(self):
        self.canvas.delete("route_left", "route_shortest", "route_straightest", "route_diagonal", "route_smoothed")
        if self.mouse_sim_running or self.sim_paused: return
        visibility_map = { "route_left": self.show_route_left_var, "route_shortest": self.show_route_shortest_var, "route_diagonal": self.show_route_diagonal_var, "route_straightest": self.show_route_straightest_var, "route_smoothed": self.show_route_smoothed_var }
        line_options_sharp = {'width': ROUTE_WIDTH, 'capstyle': tk.BUTT}; line_options_shortest = {'width': ROUTE_WIDTH + 2, 'capstyle': tk.ROUND}; line_options_round = {'width': ROUTE_WIDTH, 'capstyle': tk.ROUND}; line_options_straightest = {'width': ROUTE_WIDTH, 'capstyle': tk.ROUND}; line_options_smoothed = {'width': ROUTE_WIDTH, 'capstyle': tk.ROUND, 'dash': (4, 4)}
        paths_colors_tags_basic = [(self.route_path_shortest, COLOR_ROUTE_SHORTEST, "route_shortest"), (self.route_path_diagonal, COLOR_ROUTE_DIAGONAL, "route_diagonal"), (self.route_path_left, COLOR_ROUTE_LEFT, "route_left")]
        for path, color, tag in paths_colors_tags_basic:
            visibility_var = visibility_map.get(tag)
            if not visibility_var or not visibility_var.get() or not path: continue
            if tag == "route_left":
                 if len(path) < 2: continue
                 points = [coord for r,c in path for coord in self.cell_center_to_pixel(r,c)]
                 if len(points) >= 4: self.canvas.create_line(points, fill=color, tags=tag, **line_options_sharp)
            else:
                path_vertices = self._calculate_pixel_vertices(path)
                if len(path_vertices) >= 2:
                     current_line_options = line_options_shortest if tag == "route_shortest" else line_options_round
                     segment_points_flat = [coord for point in path_vertices for coord in point]
                     self.canvas.create_line(segment_points_flat, fill=color, tags=tag, **current_line_options)
        if visibility_map["route_straightest"].get() and len(self.straightest_path_pixel_vertices) >= 2:
            straightest_points_flat = [coord for point in self.straightest_path_pixel_vertices for coord in point]
            self.canvas.create_line(straightest_points_flat, fill=COLOR_ROUTE_STRAIGHTEST, tags="route_straightest", **line_options_straightest)
        if SCIPY_AVAILABLE and visibility_map["route_smoothed"].get() and len(self.straightest_path_pixel_vertices) >= 4:
            try:
                x_pts, y_pts = zip(*self.straightest_path_pixel_vertices); coords = np.array([x_pts, y_pts])
                current_cell_size = float(self.cell_visual_size_px); default_cell_size = float(DEFAULT_CELL_VISUAL_SIZE_PX)
                adj_s = BASE_SMOOTHING_FACTOR * (current_cell_size / default_cell_size)**2 if default_cell_size > 1e-6 else BASE_SMOOTHING_FACTOR
                tck, u = splprep(coords, s=max(0, adj_s), k=3, per=0)
                u_fine = np.linspace(u.min(), u.max(), max(50, len(x_pts) * 5))
                x_smooth, y_smooth = splev(u_fine, tck)
                smooth_points_flat = [c for p in zip(x_smooth, y_smooth) for c in p]
                if len(smooth_points_flat) >= 4: self.canvas.create_line(smooth_points_flat, fill=COLOR_ROUTE_SMOOTHED, tags="route_smoothed", **line_options_smoothed)
            except Exception as e: print(f"Error smoothing route: {e}"); self.update_status("Error smoothing route.")

    # --- Maze Generation ---
    def _get_neighbours(self, r, c, visited):
        neighbours = []; gs = self.grid_size
        for direction4 in range(4):
            nr, nc = r + DR4[direction4], c + DC4[direction4]
            if 0 <= nr < gs and 0 <= nc < gs and not visited[nr][nc]: neighbours.append(((nr, nc), direction4))
        return neighbours
    def _remove_wall(self, r, c, direction4):
        try:
            if direction4 == N4:   self.h_walls[r][c] = False
            elif direction4 == E4: self.v_walls[r][c+1] = False
            elif direction4 == S4: self.h_walls[r+1][c] = False
            elif direction4 == W4: self.v_walls[r][c] = False
        except IndexError: pass
    def _recursive_backtracker_generate(self):
        gs = self.grid_size; visited = [[False for _ in range(gs)] for _ in range(gs)]
        stack = deque(); gen_start_r, gen_start_c = self.start_cell
        visited[gen_start_r][gen_start_c] = True; stack.append((gen_start_r, gen_start_c))
        if gen_start_r == gs - 1 and gen_start_c == 0:
            self._remove_wall(gen_start_r, gen_start_c, N4)
            first_move_r, first_move_c = gen_start_r + DR4[N4], gen_start_c + DC4[N4]
            if 0 <= first_move_r < gs and 0 <= first_move_c < gs: visited[first_move_r][first_move_c] = True; stack.append((first_move_r, first_move_c))
        while stack:
            r, c = stack[-1]; neighbours = self._get_neighbours(r, c, visited)
            if neighbours: (nr, nc), direction = random.choice(neighbours); self._remove_wall(r, c, direction); visited[nr][nc] = True; stack.append((nr, nc))
            else: stack.pop()
    def _add_loops(self, probability):
        gs = self.grid_size
        for r in range(1, gs):
            for c in range(gs):
                if self.h_walls[r][c] and random.random() < probability: self.h_walls[r][c] = False
        for r in range(gs):
            for c in range(1, gs):
                 if self.v_walls[r][c] and random.random() < probability: self.v_walls[r][c] = False
    def _is_true_center_post(self, r_post, c_post): return r_post == self.grid_size // 2 and c_post == self.grid_size // 2
    def add_wall_safe(self, wall_type, r_idx, c_idx):
        gs = self.grid_size
        try:
            if wall_type == 'h':
                if self._is_true_center_post(r_idx, c_idx) or self._is_true_center_post(r_idx, c_idx + 1): return
                if 0 < r_idx < gs and 0 <= c_idx < gs: self.h_walls[r_idx][c_idx] = True
            elif wall_type == 'v':
                if self._is_true_center_post(r_idx, c_idx) or self._is_true_center_post(r_idx + 1, c_idx): return
                if 0 <= r_idx < gs and 0 < c_idx < gs: self.v_walls[r_idx][c_idx] = True
        except IndexError: pass
    def remove_walls_around_post(self, r_post, c_post):
        gs = self.grid_size
        try:
            if c_post > 0: self.h_walls[r_post][c_post-1] = False
            if c_post < gs: self.h_walls[r_post][c_post] = False
            if r_post > 0: self.v_walls[r_post-1][c_post] = False
            if r_post < gs: self.v_walls[r_post][c_post] = False
        except IndexError: pass
    def _ensure_post_connectivity(self):
        gs = self.grid_size; center_r, center_c = gs // 2, gs // 2
        for r_post in range(1, gs):
            for c_post in range(1, gs):
                if r_post == center_r and c_post == center_c: continue
                connected = 0; possible = []
                if c_post > 0: (connected := connected + 1) if self.h_walls[r_post][c_post-1] else possible.append(('h', r_post, c_post-1))
                if c_post < gs: (connected := connected + 1) if self.h_walls[r_post][c_post] else possible.append(('h', r_post, c_post))
                if r_post > 0: (connected := connected + 1) if self.v_walls[r_post-1][c_post] else possible.append(('v', r_post-1, c_post))
                if r_post < gs: (connected := connected + 1) if self.v_walls[r_post][c_post] else possible.append(('v', r_post, c_post))
                if connected == 0 and possible: self.add_wall_safe(*random.choice(possible))
    def _is_reachable(self, target_r, target_c):
        q = deque([self.start_cell]); visited = {self.start_cell}; gs = self.grid_size
        while q:
            r, c = q.popleft()
            if r == target_r and c == target_c: return True
            for dir4 in range(4):
                if not self.has_wall(r, c, dir4):
                    nr, nc = r + DR4[dir4], c + DC4[dir4]
                    if (0 <= nr < gs and 0 <= nc < gs and (nr, nc) not in visited): visited.add((nr, nc)); q.append((nr, nc))
        return False
    def generate_maze(self):
        if not self._check_save_before_action("generating new maze"): return
        try:
            target_size = int(self.selected_size_var.get())
            if target_size != self.grid_size:
                 if not self._check_save_before_action("changing size for generation"): self.selected_size_var.set(str(self.grid_size)); return
                 if not self._set_grid_size(target_size): return
        except ValueError: pass
        self.show_sim_results = False
        gs = self.grid_size
        if not self.goal_cells:
            messagebox.showwarning("Generation Warning", "No goal cells defined.\nPlease Shift+Click to set goal(s) first.", parent=self.master); return
        max_attempts = 20 + (gs // 16 - 1) * 10
        for attempt in range(1, max_attempts + 1):
            self.update_status(f"Generating {gs}x{gs} maze (Attempt {attempt})..."); self.master.update()
            self._initialize_all_walls(); self._recursive_backtracker_generate()
            self._add_loops(MAZE_GENERATION_LOOP_PROBABILITY); self._ensure_post_connectivity()
            start_r, start_c = self.start_cell
            try: self.h_walls[start_r][start_c]=False; self.v_walls[start_r][start_c+1]=True
            except IndexError: pass
            goal_reachable = any(self._is_reachable(gr, gc) for gr,gc in self.goal_cells)
            if goal_reachable:
                self.current_maze_file=None; self.maze_modified=True; self._update_window_title(); self.find_and_draw_routes()
                self.update_status(f"Maze generated successfully (Attempt {attempt})."); return
            else: self.update_status(f"Attempt {attempt} failed reachability. Retrying...")
        messagebox.showerror("Generation Error", f"Failed after {max_attempts} attempts.", parent=self.master); self.update_status("Generation failed.");
    def save_maze_text(self):
        gs = self.grid_size
        filename = filedialog.asksaveasfilename(defaultextension=".txt", filetypes=[("Text files", "*.txt"), ("Maze files", "*.maze"), ("All files", "*.*")], title="Save Maze As Text File", initialfile=f"maze{gs}x{gs}_{time.strftime('%Y%m%d_%H%M%S')}.txt")
        if not filename: return False
        output_lines = []
        for out_r in range(2 * gs + 1):
            row_str = ""; r_wall = out_r // 2; r_cell = (out_r - 1) // 2
            if out_r % 2 == 0:
                row_str += "o"
                for c in range(gs):
                    has_wall = self.h_walls[r_wall][c] if 0<=r_wall<len(self.h_walls) and 0<=c<len(self.h_walls[0]) else False
                    row_str += ("---" if has_wall else "   ") + "o"
            else:
                for c in range(gs + 1):
                    has_wall = self.v_walls[r_cell][c] if 0<=r_cell<len(self.v_walls) and 0<=c<len(self.v_walls[0]) else False
                    row_str += "|" if has_wall else " "
                    if c < gs: row_str += (" S " if (r_cell,c)==self.start_cell else (" G " if (r_cell,c) in self.goal_cells else "   "))
            output_lines.append(row_str)
        try:
            with open(filename, 'w') as f: f.write("\n".join(output_lines))
            self.current_maze_file = filename; self.maze_modified = False; self._update_window_title()
            self.update_status(f"Maze saved to {os.path.basename(filename)}"); return True
        except Exception as e: messagebox.showerror("Save Error", f"Failed save:\n{e}", parent=self.master); self.update_status("Save failed."); return False
    def load_maze_text(self):
        if not self._check_save_before_action("loading"): return
        filename = filedialog.askopenfilename(filetypes=[("Text/Maze files", "*.txt *.maze"), ("All files", "*.*")], title="Load Maze File")
        if not filename: return
        self.show_sim_results = False
        try:
            with open(filename, 'r') as f: lines = [line.rstrip() for line in f if line.strip()]
            detected_size = -1
            if len(lines) == 2*16+1: detected_size=16
            elif len(lines) == 2*32+1: detected_size=32
            else: raise ValueError(f"Unsupported row count ({len(lines)}).")
            expected_cols = 4*detected_size+1
            if not lines or len(lines[0])<expected_cols: raise ValueError(f"Invalid column count.")
            if self.grid_size != detected_size:
                if not self._set_grid_size(detected_size): raise RuntimeError("Failed to set size.")
            gs = self.grid_size
            new_h=[[False for _ in range(gs)] for _ in range(gs+1)]; new_v=[[False for _ in range(gs+1)] for _ in range(gs)]
            loaded_goal_cells = set()
            loaded_start_cell = None
            for r_idx, line in enumerate(lines):
                if r_idx%2==0: # H walls
                    r_wall = r_idx//2
                    if 0<=r_wall<=gs:
                        for c in range(gs): char_idx=c*4+2; new_h[r_wall][c]=(line[char_idx]=='-') if char_idx<len(line) else False
                else: # V walls & Cells
                    r_cell=(r_idx-1)//2
                    if 0<=r_cell<gs:
                        for c in range(gs+1):
                            char_idx=c*4; new_v[r_cell][c]=(line[char_idx]=='|') if char_idx<len(line) else False
                            if c < gs: # Cell content
                                content_idx = c*4 + 1
                                if content_idx + 2 < len(line):
                                    content = line[content_idx:content_idx+3]
                                    if content == " G ": loaded_goal_cells.add((r_cell, c))
                                    elif content == " S ": loaded_start_cell = (r_cell, c)
            self.h_walls=new_h; self.v_walls=new_v; self.initialize_outer_walls()
            self.goal_cells = loaded_goal_cells if loaded_goal_cells else self._default_goal_cells.copy()
            self.start_cell = loaded_start_cell if loaded_start_cell is not None else (gs - 1, 0)
            self.start_pos_lh = (self.start_cell[0], self.start_cell[1], N4)
            self.current_maze_file=filename; self.maze_modified=False
            self._update_window_title(); self.find_and_draw_routes()
            self.update_status(f"Loaded {gs}x{gs} maze: {os.path.basename(filename)}")
        except FileNotFoundError: messagebox.showerror("Load Error", f"File not found:\n{filename}", parent=self.master); self.update_status("Load failed: File not found."); self.current_maze_file=None; self.maze_modified=False; self._update_window_title()
        except ValueError as e: messagebox.showerror("Load Error", f"Invalid format/size:\n{e}", parent=self.master); self.update_status(f"Load failed: {e}"); self.current_maze_file=None; self.maze_modified=False; self._update_window_title()
        except Exception as e: messagebox.showerror("Load Error", f"Unexpected error:\n{e}", parent=self.master); self.update_status("Load failed."); self.current_maze_file=None; self.maze_modified=False; self._update_window_title()

    # --- GitHub Download ---
    def fetch_github_maze_list(self):
        """Opens the dialog to browse and load mazes from GitHub."""
        if not self._check_save_before_action("loading from GitHub"): return
        self._show_download_selection_dialog() # Dialog handles fetching

    def _show_download_selection_dialog(self):
        """Creates a Toplevel window to select maze size and file, including preview."""
        dialog = Toplevel(self.master); dialog.title("Load Maze from GitHub"); dialog.geometry("550x480"); dialog.transient(self.master); dialog.grab_set()
        dialog_size_var = tk.StringVar(value=self.selected_size_var.get())
        maze_files_dict = {}
        current_sorted_filenames = []
        self.preview_canvas = None; self.preview_after_id = None; self.selected_maze_url = None
        main_frame = Frame(dialog); main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        main_frame.rowconfigure(2, weight=1); main_frame.columnconfigure(0, weight=1); main_frame.columnconfigure(1, weight=0)
        top_frame = Frame(main_frame); top_frame.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 10))
        size_select_frame = Frame(top_frame, bd=1, relief=tk.GROOVE); size_select_frame.pack(side=tk.LEFT, padx=0)
        Label(size_select_frame, text="Maze Size:").pack(side=tk.LEFT, padx=(5,2))
        tk.Radiobutton(size_select_frame, text="16x16", variable=dialog_size_var, value="16", command=lambda: _fetch_list_and_update_ui(dialog, listbox, dialog_size_var, maze_files_dict)).pack(side=tk.LEFT)
        tk.Radiobutton(size_select_frame, text="32x32", variable=dialog_size_var, value="32", command=lambda: _fetch_list_and_update_ui(dialog, listbox, dialog_size_var, maze_files_dict)).pack(side=tk.LEFT, padx=(0,5))
        search_frame = Frame(main_frame); search_frame.grid(row=1, column=0, columnspan=2, sticky="ew", pady=(0, 5))
        Label(search_frame, text="Search:").pack(side=tk.LEFT); search_var = StringVar(); search_entry = Entry(search_frame, textvariable=search_var, width=40); search_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(5,0))
        list_frame = Frame(main_frame); list_frame.grid(row=2, column=0, sticky="nsew", padx=(0, 5)); scrollbar = Scrollbar(list_frame, orient=tk.VERTICAL); scrollbar.pack(side=tk.RIGHT, fill=tk.Y); listbox = Listbox(list_frame, yscrollcommand=scrollbar.set, exportselection=False, selectmode=SINGLE); listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True); scrollbar.config(command=listbox.yview)
        preview_frame = Frame(main_frame, bd=1, relief=tk.SUNKEN); preview_frame.grid(row=2, column=1, sticky="nsew", padx=(5, 0)); PREVIEW_SIZE = 180; self.preview_canvas = Canvas(preview_frame, width=PREVIEW_SIZE, height=PREVIEW_SIZE, bg="white", bd=0, highlightthickness=0); self.preview_canvas.pack(padx=2, pady=2);
        button_frame = Frame(main_frame); button_frame.grid(row=3, column=0, columnspan=2, pady=(10, 0)); Button(button_frame, text="Load Selected", command=lambda: on_load_confirm(listbox, maze_files_dict, dialog), width=12).pack(side=tk.LEFT, padx=10); Button(button_frame, text="Cancel", command=dialog.destroy, width=12).pack(side=tk.LEFT, padx=10)

        def _fetch_list_and_update_ui(parent_dialog, lb, size_var, files_dict_ref):
            nonlocal current_sorted_filenames
            lb.delete(0, END); files_dict_ref.clear(); search_var.set("")
            if self.preview_canvas: self.preview_canvas.delete("all")
            if self.preview_after_id: parent_dialog.after_cancel(self.preview_after_id); self.preview_after_id = None
            self.selected_maze_url = None
            size_str = size_var.get()
            repo_subpath = "classic" if size_str == "16" else "halfsize"
            api_url = f"https://api.github.com/repos/micromouseonline/mazefiles/contents/{repo_subpath}"
            if self.preview_canvas: self.preview_canvas.create_text(PREVIEW_SIZE/2, PREVIEW_SIZE/2, text=f"Fetching {size_str}x{size_str}\nlist...", justify=tk.CENTER, fill="blue")
            parent_dialog.update_idletasks()
            try:
                response = requests.get(api_url, timeout=15); response.raise_for_status(); data = response.json()
                if not isinstance(data, list): raise ValueError("Invalid API response")
                files_dict_ref.clear()
                for item in data:
                    if isinstance(item,dict) and item.get('type')=='file' and item.get('name','').lower().endswith((".txt",".maze")) and item.get('download_url'):
                         files_dict_ref[item['name']] = item['download_url']
                current_sorted_filenames = sorted(files_dict_ref.keys(), key=str.lower)
                for name in current_sorted_filenames: lb.insert(END, name)
                if self.preview_canvas:
                     self.preview_canvas.delete("all")
                     msg = "Select a maze\nto preview" if files_dict_ref else f"No {size_str}x{size_str} mazes\nfound in repo."
                     clr = "grey" if files_dict_ref else "orange"
                     self.preview_canvas.create_text(PREVIEW_SIZE/2, PREVIEW_SIZE/2, text=msg, justify=tk.CENTER, fill=clr)
            except (requests.exceptions.RequestException, ValueError, Exception) as e:
                 err_msg = f"Error fetching list:\n{type(e).__name__}"
                 if self.preview_canvas and self.preview_canvas.winfo_exists():
                      self.preview_canvas.delete("all"); self.preview_canvas.create_text(PREVIEW_SIZE/2, PREVIEW_SIZE/2, text=err_msg, justify=tk.CENTER, fill="red")
                 print(f"Error fetching GitHub list: {e}")

        def _update_listbox_filter(*args):
            search_term = search_var.get().lower().strip(); listbox.delete(0, END)
            for filename in current_sorted_filenames:
                if not search_term or search_term in filename.lower(): listbox.insert(END, filename)
            if self.preview_canvas: self.preview_canvas.delete("all"); self.preview_canvas.create_text(PREVIEW_SIZE/2, PREVIEW_SIZE/2, text="(Filter active)", fill="grey")
            if self.preview_after_id: dialog.after_cancel(self.preview_after_id); self.preview_after_id = None
            self.selected_maze_url = None
        search_var.trace_add("write", _update_listbox_filter)

        def _fetch_and_draw_preview(filename, url):
            if not self.preview_canvas or not self.preview_canvas.winfo_exists(): return
            self.preview_canvas.delete("all"); self.preview_canvas.create_text(PREVIEW_SIZE/2, PREVIEW_SIZE/2, text=f"Loading\n{filename}...", justify=tk.CENTER, fill="blue"); self.preview_canvas.update_idletasks()
            try:
                response = requests.get(url, timeout=10); response.raise_for_status()
                content = response.text; lines = content.splitlines(); lines = [line.rstrip() for line in lines if line.strip()]
                preview_grid_size = -1
                if len(lines)==2*16+1: preview_grid_size=16
                elif len(lines)==2*32+1: preview_grid_size=32
                else: raise ValueError(f"Invalid rows")
                expected_cols = 4*preview_grid_size+1
                if not lines or len(lines[0])<expected_cols: raise ValueError(f"Invalid cols")
                gs = preview_grid_size
                h_w=[[False for _ in range(gs)] for _ in range(gs+1)]; v_w=[[False for _ in range(gs+1)] for _ in range(gs)]
                for r_idx, line in enumerate(lines):
                    if r_idx%2==0:
                        r_wall = r_idx//2
                        if 0<=r_wall<=gs:
                            for c in range(gs): char_idx=c*4+2; h_w[r_wall][c]=(line[char_idx]=='-') if char_idx<len(line) else False
                    else:
                        r_cell=(r_idx-1)//2
                        if 0<=r_cell<gs:
                            for c in range(gs+1): char_idx=c*4; v_w[r_cell][c]=(line[char_idx]=='|') if char_idx<len(line) else False
                self._draw_maze_on_canvas(self.preview_canvas, h_w, v_w, PREVIEW_SIZE, grid_size_override=gs)
            except (requests.exceptions.RequestException, ValueError, IndexError, Exception) as e:
                 if self.preview_canvas and self.preview_canvas.winfo_exists():
                     self.preview_canvas.delete("all"); err_msg = f"Preview Error:\n{type(e).__name__}"
                     if isinstance(e, requests.exceptions.Timeout): err_msg = "Preview Error:\nTimeout"
                     elif isinstance(e, requests.exceptions.ConnectionError): err_msg = "Preview Error:\nNetwork"
                     elif isinstance(e, ValueError): err_msg = "Preview Error:\nInvalid Format/Size"
                     self.preview_canvas.create_text(PREVIEW_SIZE/2, PREVIEW_SIZE/2, text=err_msg, justify=tk.CENTER, fill="red")
        def _on_preview_selection(event=None):
            if self.preview_after_id: dialog.after_cancel(self.preview_after_id); self.preview_after_id = None
            idx = listbox.curselection()
            if not idx:
                if self.preview_canvas: self.preview_canvas.delete("all"); self.preview_canvas.create_text(PREVIEW_SIZE/2, PREVIEW_SIZE/2, text="(No selection)", fill="grey")
                self.selected_maze_url = None; return
            filename = listbox.get(idx[0]); url = maze_files_dict.get(filename); self.selected_maze_url = url
            if url: self.preview_after_id = dialog.after(300, lambda u=url, f=filename: _fetch_and_draw_preview(f, u))
            else:
                if self.preview_canvas: self.preview_canvas.delete("all"); self.preview_canvas.create_text(PREVIEW_SIZE/2, PREVIEW_SIZE/2, text="Error:\nURL missing?", fill="red")
                self.selected_maze_url = None
        listbox.bind("<<ListboxSelect>>", _on_preview_selection)
        def on_load_confirm(lb, files_dict, dlg):
            idx = lb.curselection(); filename=lb.get(idx[0]) if idx else None; url=files_dict.get(filename) if filename else None
            if url: dlg.destroy(); self._download_and_load_selected_maze(filename, url)
            else: messagebox.showwarning("Select", "Please select a maze file.", parent=dlg)
        listbox.bind("<Double-1>", lambda e:on_load_confirm(listbox, maze_files_dict, dialog)); listbox.bind("<Return>", lambda e:on_load_confirm(listbox, maze_files_dict, dialog))
        _fetch_list_and_update_ui(dialog, listbox, dialog_size_var, maze_files_dict) # Initial fetch
        search_entry.focus_set(); dialog.wait_window()

    def _draw_maze_on_canvas(self, target_canvas, h_walls, v_walls, target_size_px, grid_size_override=None):
        """Draws a simplified maze representation onto a given canvas."""
        target_canvas.delete("all")
        gs = grid_size_override if grid_size_override is not None else self.grid_size
        if not h_walls or not v_walls or target_size_px <= 10 or gs <= 0:
             target_canvas.create_text(target_size_px/2, target_size_px/2, text="Invalid Data\nfor Preview", justify=tk.CENTER, fill="orange"); return
        preview_margin = max(3, int(target_size_px * 0.04)); drawable_size = target_size_px - 2 * preview_margin
        if drawable_size <= 0: return
        cell_size = drawable_size / gs
        wall_color = "#555"; wall_thickness = 1
        try:
            for r in range(gs + 1): # H walls
                for c in range(gs):
                    if r < len(h_walls) and c < len(h_walls[r]) and h_walls[r][c]:
                        x0=preview_margin+c*cell_size; y0=preview_margin+r*cell_size; x1=x0+cell_size; y1=y0
                        target_canvas.create_line(x0,y0,x1,y1, fill=wall_color, width=wall_thickness, tags="preview_wall")
            for r in range(gs): # V walls
                for c in range(gs + 1):
                     if r < len(v_walls) and c < len(v_walls[r]) and v_walls[r][c]:
                        x0=preview_margin+c*cell_size; y0=preview_margin+r*cell_size; x1=x0; y1=y0+cell_size
                        target_canvas.create_line(x0,y0,x1,y1, fill=wall_color, width=wall_thickness, tags="preview_wall")
        except IndexError: target_canvas.delete("all"); target_canvas.create_text(target_size_px/2, target_size_px/2, text="Preview Error:\nIndex Error", justify=tk.CENTER, fill="red")
        except Exception as e: target_canvas.delete("all"); target_canvas.create_text(target_size_px/2, target_size_px/2, text=f"Preview Error:\n{type(e).__name__}", justify=tk.CENTER, fill="red")

    def _download_and_load_selected_maze(self, filename, download_url):
        self.update_status(f"Downloading '{filename}'..."); self.master.update()
        self.show_sim_results = False
        try:
            response = requests.get(download_url, timeout=15); response.raise_for_status(); content = response.text
            lines = content.splitlines(); lines = [line.rstrip() for line in lines if line.strip()]
            detected_size = -1
            if len(lines)==2*16+1: detected_size=16
            elif len(lines)==2*32+1: detected_size=32
            else: raise ValueError(f"Unsupported row count ({len(lines)}).")
            expected_cols = 4*detected_size+1
            if not lines or len(lines[0])<expected_cols: raise ValueError(f"Invalid column count.")
            if self.grid_size != detected_size:
                self.selected_size_var.set(str(detected_size))
            gs = int(self.selected_size_var.get())
            new_h=[[False for _ in range(gs)] for _ in range(gs+1)]; new_v=[[False for _ in range(gs+1)] for _ in range(gs)]
            loaded_goal_cells = set()
            loaded_start_cell = None
            for r_idx, line in enumerate(lines):
                if r_idx%2==0:
                    r_wall = r_idx//2
                    if 0<=r_wall<=gs:
                        for c in range(gs): char_idx=c*4+2; new_h[r_wall][c]=(line[char_idx]=='-') if char_idx<len(line) else False
                else:
                    r_cell=(r_idx-1)//2
                    if 0<=r_cell<gs:
                        for c in range(gs+1):
                            char_idx=c*4; new_v[r_cell][c]=(line[char_idx]=='|') if char_idx<len(line) else False
                            if c < gs:
                                content_idx = c*4 + 1
                                if content_idx + 2 < len(line):
                                    content = line[content_idx:content_idx+3]
                                    if content == " G ": loaded_goal_cells.add((r_cell, c))
                                    elif content == " S ": loaded_start_cell = (r_cell, c)
            self.h_walls=new_h; self.v_walls=new_v; self.initialize_outer_walls()
            self.goal_cells = loaded_goal_cells if loaded_goal_cells else self._default_goal_cells.copy()
            self.start_cell = loaded_start_cell if loaded_start_cell is not None else (gs - 1, 0)
            self.start_pos_lh = (self.start_cell[0], self.start_cell[1], N4)
            self.current_maze_file = f"GitHub: {filename}"; self.maze_modified=False
            self._update_window_title(); self.find_and_draw_routes()
            self.update_status(f"Loaded {gs}x{gs} maze '{filename}' from GitHub.")
        except requests.exceptions.Timeout: messagebox.showerror("Error", f"Timeout dl '{filename}'.", parent=self.master); self.update_status("Download failed (timeout)."); self.current_maze_file=None; self.maze_modified=False; self._update_window_title()
        except requests.exceptions.RequestException as e: messagebox.showerror("Error", f"Network error dl:\n{e}", parent=self.master); self.update_status("Download failed (network)."); self.current_maze_file=None; self.maze_modified=False; self._update_window_title()
        except ValueError as e: messagebox.showerror("Error", f"Invalid format/size '{filename}':\n{e}", parent=self.master); self.update_status(f"Load failed: {e}"); self.current_maze_file=None; self.maze_modified=False; self._update_window_title()
        except Exception as e: messagebox.showerror("Error", f"Failed process '{filename}':\n{e}", parent=self.master); self.update_status("Load failed."); self.current_maze_file=None; self.maze_modified=False; self._update_window_title()

    def update_status(self, message):
        self.status_label.config(text=message)

    # --- Mouse Simulation Methods ---
    def _save_sim_state(self):
        """Saves the current simulation state to the history."""
        state = {
            'phase': self.mouse_sim_phase, 'run_count': self.mouse_run_count,
            'r': self.mouse_r, 'c': self.mouse_c, 'dir4': self.mouse_dir4,
            'seen_h': [row[:] for row in self.mouse_seen_h_walls],
            'seen_v': [row[:] for row in self.mouse_seen_v_walls],
            'trail': self.mouse_trail[:], 'walls_seen_count': self.mouse_walls_seen_count,
            'status_text': self.status_label.cget("text")
        }
        # If we have stepped back, new actions create a new timeline
        if self.sim_history_index < len(self.sim_history) - 1:
            self.sim_history = self.sim_history[:self.sim_history_index + 1]
        self.sim_history.append(state)
        self.sim_history_index += 1

    def _load_sim_state(self, index):
        """Loads a simulation state from history and updates the view."""
        if not (0 <= index < len(self.sim_history)): return
        self.sim_history_index = index
        state = self.sim_history[index]
        self.mouse_sim_phase = state['phase']
        self.mouse_run_count = state['run_count']
        self.mouse_r = state['r']; self.mouse_c = state['c']; self.mouse_dir4 = state['dir4']
        self.mouse_seen_h_walls = state['seen_h']; self.mouse_seen_v_walls = state['seen_v']
        self.mouse_trail = state['trail']; self.mouse_walls_seen_count = state['walls_seen_count']
        self.update_status(state['status_text'])
        self._draw_simulation_state()
        self._update_sim_button_states()

    def _update_sim_button_states(self):
        """Updates the enabled/disabled state and text of simulation buttons."""
        # This check ensures that if we stop the sim, the buttons don't try to update
        if not (self.mouse_sim_running or self.sim_paused): return
        
        self.sim_pause_button.config(text='▶' if self.sim_paused else '⏸')
        back_state = tk.NORMAL if self.sim_paused and self.sim_history_index > 0 else tk.DISABLED
        self.sim_back_button.config(state=back_state)
        
        # Forward button is enabled if paused and not at the end of history,
        # OR if paused at the end but the sim can still calculate more steps.
        is_at_end = self.sim_history_index >= len(self.sim_history) - 1
        can_run_more = self.mouse_sim_running
        forward_state = tk.DISABLED
        if self.sim_paused:
            if not is_at_end:
                forward_state = tk.NORMAL # Can step forward through history
            elif can_run_more:
                forward_state = tk.NORMAL # Can execute a new step
        self.sim_forward_button.config(state=forward_state)

    def _toggle_sim_pause(self):
        """Toggles the paused state of the simulation."""
        if not (self.mouse_sim_running or self.sim_paused): return
        # If the sim is already finished (running=False, paused=True), we don't allow unpausing.
        if not self.mouse_sim_running and self.sim_paused:
            return

        self.sim_paused = not self.sim_paused
        self._update_sim_button_states()
        if not self.sim_paused:
            # We are unpausing, resume the automatic simulation loop
            self._mouse_simulation_step() 

    def _sim_step_forward(self):
        """Moves the simulation forward by one step, either from history or by calculating a new step."""
        if not self.sim_paused: return
        is_at_end = self.sim_history_index >= len(self.sim_history) - 1
        
        if not is_at_end:
            # We are not at the end, so just load the next historical state.
            self._load_sim_state(self.sim_history_index + 1)
        elif self.mouse_sim_running:
            # We are at the end of history, but the simulation is not yet complete.
            # Execute one new step manually.
            self._execute_one_sim_step()

    def _sim_step_backward(self):
        """Moves the simulation backward by one step from history."""
        if not self.sim_paused: return
        if self.sim_history_index > 0:
            self._load_sim_state(self.sim_history_index - 1)

    def stop_mouse_simulation(self, user_stopped=True):
        """Stops the current mouse simulation and cleans up the GUI."""
        was_active = self.mouse_sim_running or self.sim_paused
        
        self.mouse_sim_running = False
        self.sim_paused = False
        if self.mouse_after_id:
            self.master.after_cancel(self.mouse_after_id)
            self.mouse_after_id = None
        
        if was_active: 
            if user_stopped:
                self.update_status("Mouse simulation stopped by user.")
            
            # Restore GUI
            self.sim_controls_frame.pack_forget()
            self.simulate_button.pack(side=tk.LEFT, padx=10)
            
            self.show_sim_results = False
            self.find_and_draw_routes()

    def start_mouse_simulation(self):
        """Starts a new mouse simulation run."""
        if self.mouse_sim_running or self.sim_paused:
            self.stop_mouse_simulation(user_stopped=True)
            return
        if not self.goal_cells:
            messagebox.showwarning("Simulation Error", "No goal cells defined. Shift+Click to set goals.", parent=self.master)
            return
        # --- Setup ---
        self.mouse_sim_running = True
        self.sim_paused = False
        self.show_sim_results = False
        self.sim_history = []
        self.sim_history_index = -1
        # --- Initial State ---
        self.mouse_sim_phase = "EXPLORE"
        self.mouse_run_count = 1
        self.mouse_r, self.mouse_c = self.start_cell
        self.mouse_dir4 = N4
        self.mouse_trail = [(self.mouse_r, self.mouse_c)]
        gs = self.grid_size
        self.mouse_seen_h_walls = [[False for _ in range(gs)] for _ in range(gs + 1)]
        self.mouse_seen_v_walls = [[False for _ in range(gs + 1)] for _ in range(gs)]
        for c_idx in range(gs): self.mouse_seen_h_walls[0][c_idx] = self.mouse_seen_h_walls[gs][c_idx] = True
        for r_idx in range(gs): self.mouse_seen_v_walls[r_idx][0] = self.mouse_seen_v_walls[r_idx][gs] = True
        self.mouse_walls_seen_count = self._count_seen_walls() # Initialize count
        self._update_seen_walls()
        self.update_status(f"Run {self.mouse_run_count} ({self.mouse_sim_phase}): Starting exploration...")
        # --- GUI Update ---
        self.simulate_button.pack_forget()
        self.sim_controls_frame.pack(side=tk.LEFT, padx=10)
        self.canvas.delete("route_left", "route_shortest", "route_straightest", "route_diagonal", "route_smoothed")
        # --- Save Initial State and Start ---
        self._save_sim_state() # Save state 0
        self._draw_simulation_state()
        self._update_sim_button_states()
        self.mouse_after_id = self.master.after(50, self._mouse_simulation_step)

    def _mouse_simulation_step(self):
        """The timer-based loop for the simulation. Calls the core logic if not paused."""
        if not self.mouse_sim_running: 
            if self.mouse_after_id: self.master.after_cancel(self.mouse_after_id); self.mouse_after_id = None
            return
        if self.sim_paused:
            if self.mouse_after_id: self.master.after_cancel(self.mouse_after_id); self.mouse_after_id = None
            return

        # Execute the logic for one step
        self._execute_one_sim_step()
        
        # Schedule the next step if the simulation is still running
        if self.mouse_sim_running:
            self.mouse_after_id = self.master.after(10, self._mouse_simulation_step)

    def _execute_one_sim_step(self):
        """
        Calculates and executes a single step of the simulation logic.
        This is the core logic, separated to be called manually or by the timer loop.
        """
        gs = self.grid_size
        r, c, direction = self.mouse_r, self.mouse_c, self.mouse_dir4
        self._update_seen_walls()

        if self.mouse_sim_phase == "EXPLORE":
            if (r, c) in self.goal_cells:
                self.update_status(f"Run {self.mouse_run_count} ({self.mouse_sim_phase}): Goal reached! Returning to start...")
                self.mouse_sim_phase = "RETURN_TO_START"
                self.mouse_trail = [(r,c)]
            else:
                flood_map = self._run_flood_fill_on_seen_maze()
                current_flood_val = flood_map[r][c]
                if current_flood_val == float('inf'):
                    self.update_status("Mouse is trapped! Press Stop to exit.")
                    self.mouse_sim_running = False; self.sim_paused = True
                    self._save_sim_state(); self._draw_simulation_state(); self._update_sim_button_states()
                    return
                options = []
                for move_dir in range(4):
                    if not self._mouse_has_wall_in_sim(r, c, move_dir):
                        nr, nc = r + DR4[move_dir], c + DC4[move_dir]
                        if 0 <= nr < gs and 0 <= nc < gs and flood_map[nr][nc] < current_flood_val:
                            turn_diff = abs(direction - move_dir)
                            if turn_diff == 0: turn_prio = 0
                            elif turn_diff == 2: turn_prio = 2
                            else: turn_prio = 1
                            options.append((flood_map[nr][nc], turn_prio, nr, nc, move_dir))
                if options:
                    options.sort()
                    _, _, next_r, next_c, next_dir = options[0]
                    self.mouse_r, self.mouse_c, self.mouse_dir4 = next_r, next_c, next_dir
                    self.mouse_trail.append((self.mouse_r, self.mouse_c))
                else:
                    self.update_status("Mouse trapped in local minimum. Press Stop to exit.")
                    self.mouse_sim_running = False; self.sim_paused = True
                    self._save_sim_state(); self._draw_simulation_state(); self._update_sim_button_states()
                    return
        elif self.mouse_sim_phase == "RETURN_TO_START":
            if (r, c) == self.start_cell:
                self.mouse_run_count += 1
                self.update_status(f"Run {self.mouse_run_count} (SPEED_RUN): Preparing for speed run...")
                self.mouse_sim_phase = "SPEED_RUN"
                self.mouse_trail = [(r,c)]
                self.mouse_walls_seen_count = self._count_seen_walls()
            else:
                path_to_start, _ = self._calculate_dijkstra_on_seen_maze((r,c), self.start_cell, 0.0)
                if not path_to_start or len(path_to_start) < 2:
                    self.update_status("Error: Lost! Re-exploring.")
                    self.mouse_sim_phase = "EXPLORE"
                else:
                    next_r, next_c = path_to_start[1]
                    dr, dc = next_r - r, next_c - c
                    for i in range(4):
                        if DR4[i] == dr and DC4[i] == dc: self.mouse_dir4 = i; break
                    self.mouse_r, self.mouse_c = next_r, next_c
                    self.mouse_trail.append((self.mouse_r, self.mouse_c))
        elif self.mouse_sim_phase == "SPEED_RUN":
            if (r, c) in self.goal_cells:
                new_wall_count = self._count_seen_walls()
                if new_wall_count == self.mouse_walls_seen_count:
                    # SIMULATION IS COMPLETE: Pause for final review
                    self.update_status(f"Run {self.mouse_run_count} Complete! Best route found. Press Stop to exit.")
                    self.show_sim_results = True
                    self.mouse_sim_running = False # No more steps can be calculated
                    self.sim_paused = True         # Keep UI in interactive review mode
                    self._save_sim_state()
                    self._draw_simulation_state()
                    self._update_sim_button_states() 
                    return
                else:
                    self.update_status(f"Run {self.mouse_run_count} (SPEED_RUN): New walls found. Returning to start...")
                    self.mouse_sim_phase = "RETURN_TO_START"
                    self.mouse_trail = [(r,c)]
            else:
                path_to_goal, _ = self._calculate_dijkstra_on_seen_maze((r,c), self.goal_cells, self.turn_weight_var.get())
                if not path_to_goal or len(path_to_goal) < 2:
                    self.update_status(f"Run {self.mouse_run_count} (SPEED_RUN): Path blocked! Re-exploring...")
                    self.mouse_sim_phase = "EXPLORE"
                else:
                    next_r, next_c = path_to_goal[1]
                    dr, dc = next_r - r, next_c - c
                    for i in range(4):
                        if DR4[i] == dr and DC4[i] == dc: self.mouse_dir4 = i; break
                    self.mouse_r, self.mouse_c = next_r, next_c
                    self.mouse_trail.append((self.mouse_r, self.mouse_c))
        
        # Save the new state, draw it, and update the buttons
        self._save_sim_state()
        self._draw_simulation_state()
        self._update_sim_button_states()

    def _update_seen_walls(self):
        r, c = self.mouse_r, self.mouse_c; gs = self.grid_size
        if not (0 <= r < gs and 0 <= c < gs): return
        self.mouse_seen_h_walls[r][c] = self.h_walls[r][c]
        self.mouse_seen_v_walls[r][c+1] = self.v_walls[r][c+1]
        self.mouse_seen_h_walls[r+1][c] = self.h_walls[r+1][c]
        self.mouse_seen_v_walls[r][c] = self.v_walls[r][c]
    def _mouse_has_wall_in_sim(self, r, c, direction4):
        gs = self.grid_size
        if not (0 <= r < gs and 0 <= c < gs): return True
        try:
            if direction4 == N4: return self.mouse_seen_h_walls[r][c]
            elif direction4 == E4: return self.mouse_seen_v_walls[r][c+1]
            elif direction4 == S4: return self.mouse_seen_h_walls[r+1][c]
            elif direction4 == W4: return self.v_walls[r][c]
        except IndexError: return True
        return True
    def _run_flood_fill_on_seen_maze(self):
        gs = self.grid_size
        flood_map = np.full((gs, gs), float('inf'))
        q = deque()
        for r_goal, c_goal in self.goal_cells:
            if 0 <= r_goal < gs and 0 <= c_goal < gs:
                flood_map[r_goal][c_goal] = 0
                q.append((r_goal, c_goal))
        while q:
            r, c = q.popleft()
            current_dist = flood_map[r][c]
            for dir4 in range(4):
                if not self._mouse_has_wall_in_sim(r, c, dir4):
                    nr, nc = r + DR4[dir4], c + DC4[dir4]
                    if 0 <= nr < gs and 0 <= nc < gs and flood_map[nr][nc] == float('inf'):
                        flood_map[nr][nc] = current_dist + 1
                        q.append((nr, nc))
        return flood_map

    def _calculate_dijkstra_for_weights(self, turn_weight):
        """
        Runs Dijkstra's from the goal cells on the true maze map to find the
        minimum cost to reach every cell. This is for visualization.
        Returns a 2D numpy array of costs.
        """
        gs = self.grid_size
        cost_map = np.full((gs, gs), float('inf'))
        pq = []
        visited = {} 

        for r_goal, c_goal in self.goal_cells:
            if 0 <= r_goal < gs and 0 <= c_goal < gs:
                cost_map[r_goal][c_goal] = 0
                for direction in range(4):
                    heapq.heappush(pq, (0.0, r_goal, c_goal, direction))
                    visited[(r_goal, c_goal, direction)] = 0

        while pq:
            cost, r, c, arr_dir = heapq.heappop(pq)
            if cost > cost_map[r][c]:
                continue
            
            for next_dir4 in range(4):
                if not self.has_wall(r, c, next_dir4):
                    next_r, next_c = r + DR4[next_dir4], c + DC4[next_dir4]
                    if not (0 <= next_r < gs and 0 <= next_c < gs):
                        continue

                    new_cost = cost + 1.0
                    if next_dir4 != arr_dir:
                        new_cost += turn_weight
                    
                    cost_map[next_r][next_c] = min(cost_map[next_r][next_c], new_cost)
                    
                    if new_cost < visited.get((next_r, next_c, next_dir4), float('inf')):
                         visited[(next_r, next_c, next_dir4)] = new_cost
                         heapq.heappush(pq, (new_cost, next_r, next_c, next_dir4))

        return cost_map

    def _count_seen_walls(self):
        h_count = sum(row.count(True) for row in self.mouse_seen_h_walls)
        v_count = sum(row.count(True) for row in self.mouse_seen_v_walls)
        return h_count + v_count
    def _calculate_dijkstra_on_seen_maze(self, start_node_tuple, target_nodes, turn_weight):
        gs = self.grid_size
        if isinstance(target_nodes, tuple): target_goals = {target_nodes}
        else: target_goals = target_nodes
        if start_node_tuple in target_goals:
            return [start_node_tuple], "Already at target"
        pq = [(0.0, 0.0, 0, start_node_tuple[0], start_node_tuple[1], N4, [start_node_tuple])]
        visited = {}
        while pq:
            priority, cost, turns, r, c, arr_dir, path = heapq.heappop(pq)
            if (r, c) in target_goals: return path, f"Target ({cost:.0f}c, {turns}t)"
            visited_key = (r, c, arr_dir)
            if visited_key in visited and visited[visited_key] <= priority: continue
            visited[visited_key] = priority
            for next_dir4 in range(4):
                if not self._mouse_has_wall_in_sim(r, c, next_dir4):
                    next_r, next_c = r + DR4[next_dir4], c + DC4[next_dir4]
                    if not (0 <= next_r < gs and 0 <= next_c < gs): continue
                    new_cost = cost + 1.0; turn_inc = 1 if arr_dir is not None and next_dir4 != arr_dir else 0
                    new_turns = turns + turn_inc; new_priority = new_cost + turn_weight * float(new_turns)
                    next_visited_key = (next_r, next_c, next_dir4)
                    if next_visited_key not in visited or new_priority < visited[next_visited_key]:
                        new_path = path + [(next_r, next_c)]
                        heapq.heappush(pq, (new_priority, new_cost, new_turns, next_r, next_c, next_dir4, new_path))
        return [], "Unreachable (Seen Maze)"

    def _draw_simulation_state(self):
        self.draw_maze()
        if len(self.mouse_trail) >= 2:
            trail_coords = [coord for r_cell, c_cell in self.mouse_trail for coord in self.cell_center_to_pixel(r_cell, c_cell)]
            trail_color = "magenta"
            if self.mouse_sim_phase == "EXPLORE": trail_color = "#800080"
            elif self.mouse_sim_phase == "SPEED_RUN": trail_color = "cyan"
            self.canvas.create_line(trail_coords, fill=trail_color, width=ROUTE_WIDTH, tags="mouse_trail")
        mr, mc, mdir = self.mouse_r, self.mouse_c, self.mouse_dir4
        mx, my = self.cell_center_to_pixel(mr, mc)
        cs = self.cell_visual_size_px * 0.3
        if mdir == N4: points = [mx, my - cs*0.6, mx - cs*0.5, my + cs*0.3, mx + cs*0.5, my + cs*0.3]
        elif mdir == E4: points = [mx + cs*0.6, my, mx - cs*0.3, my - cs*0.5, mx - cs*0.3, my + cs*0.5]
        elif mdir == S4: points = [mx, my + cs*0.6, mx + cs*0.5, my - cs*0.3, mx - cs*0.5, my - cs*0.3]
        else: # W4
            points = [mx - cs*0.6, my, mx + cs*0.3, my + cs*0.5, mx + cs*0.3, my - cs*0.5]
        self.canvas.create_polygon(points, fill="orange", outline="black", tags="mouse_sim_indicator")
        
        if self.master.winfo_exists():
            self.master.update_idletasks()

# --- Main Execution ---
if __name__ == "__main__":
    root = tk.Tk()
    if not SCIPY_AVAILABLE:
        print("\nWARNING: SciPy library not found. Smoothed route disabled.")
        print("Install using: pip install scipy numpy\n")
        messagebox.showwarning("Missing Dependency", "SciPy library not found.\nSmoothed route disabled.\n\nInstall using:\npip install scipy numpy", parent=root)
    app = MazeEditor(root)
    root.mainloop()