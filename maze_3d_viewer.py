import json
from ursina import *

def dot(v1, v2):
    return v1.x*v2.x + v1.y*v2.y + v1.z*v2.z

class CustomWall(Entity):
    def __init__(self, position=(0, 0, 0), scale=(1, 1, 1), main_texture=None, top_texture=None, **kwargs):
        super().__init__(
            position=position,
            scale=scale,
            collider='box'
        )
        Entity(parent=self, model='cube', texture=main_texture, color=color.white, scale=(1, 0.98, 1), position=(0, -0.01, 0))
        Entity(parent=self, model='cube', texture=top_texture, color=color.red, scale=(1, 0.02, 1), position=(0, 0.49, 0))

class CustomPost(Entity):
    def __init__(self, position=(0, 0, 0), scale=(1, 1, 1), texture=None, **kwargs):
        post_color = color.white if texture else color.yellow
        super().__init__(model='cube', texture=texture, color=post_color, position=position, scale=scale, collider='box', **kwargs)


def create_maze_from_json(json_file, textures):
    """
    Loads a Micromouse maze structure and applies textures, with correct orientation and fallbacks.
    """
    try:
        with open(json_file, 'r') as f:
            maze_data = json.load(f)
    except FileNotFoundError:
        print(f"Error: The file '{json_file}' was not found.")
        return None, 0, None
    except json.JSONDecodeError:
        print(f"Error: Could not decode the JSON file '{json_file}'.")
        return None, 0, None

    CELL_SIZE = 1.8
    WALL_HEIGHT = 0.5
    WALL_THICKNESS = 0.12
    POST_DIAMETER = 0.12
    GAP_SIZE = 0

    grid_size = maze_data.get("grid_size", 16)
    h_walls = maze_data.get("h_walls", [])
    v_walls = maze_data.get("v_walls", [])
    start_cell = [0, 0]

    offset_x = (grid_size * CELL_SIZE) / 2
    offset_z = (grid_size * CELL_SIZE) / 2

    floor_texture = textures.get('floor')
    floor_color = color.white if floor_texture else color.black

    floor = Entity(
        model='plane',
        scale=(grid_size * CELL_SIZE, 1, grid_size * CELL_SIZE),
        texture=floor_texture,
        texture_scale=(grid_size, grid_size),
        color=floor_color,
        collider='box'
    )

    wall_length = CELL_SIZE - POST_DIAMETER - (2 * GAP_SIZE)

    for y, row in enumerate(h_walls):
        for x, wall_exists in enumerate(row):
            if wall_exists:
                z_pos = (grid_size - y) * CELL_SIZE - offset_z
                pos = (x * CELL_SIZE - offset_x + CELL_SIZE / 2, WALL_HEIGHT / 2, z_pos)
                scl = (wall_length, WALL_HEIGHT, WALL_THICKNESS)
                CustomWall(position=pos, scale=scl, main_texture=textures.get('wall'), top_texture=textures.get('wall_top'))

    for y, row in enumerate(v_walls):
        for x, wall_exists in enumerate(row):
            if wall_exists:
                z_pos = ((grid_size - 1 - y) * CELL_SIZE - offset_z) + CELL_SIZE / 2
                pos = (x * CELL_SIZE - offset_x, WALL_HEIGHT / 2, z_pos)
                scl = (WALL_THICKNESS, WALL_HEIGHT, wall_length)
                CustomWall(position=pos, scale=scl, main_texture=textures.get('wall'), top_texture=textures.get('wall_top'))
    
    for y in range(grid_size + 1):
        for x in range(grid_size + 1):
            pos = (x * CELL_SIZE - offset_x, WALL_HEIGHT / 2, y * CELL_SIZE - offset_z)
            CustomPost(position=pos, scale=(POST_DIAMETER, WALL_HEIGHT, POST_DIAMETER), texture=textures.get('post'))

    start_pos_x = (start_cell[0] + 0.5) * CELL_SIZE - offset_x
    start_pos_z = (start_cell[1] + 0.5) * CELL_SIZE - offset_z
    
    return (start_pos_x, 0.5, start_pos_z), grid_size, floor


def check_collision():
    """
    Casts 4 rays to form a perfect 1x1 rectangular shield around the robot.
    """
    width = 1.0
    length = 1.0
    
    # Calculate the world-space position of the four corners
    fr = player.world_position + (player.right * width/2) + (player.forward * length/2)
    fl = player.world_position + (player.right * -width/2) + (player.forward * length/2)
    br = player.world_position + (player.right * width/2) + (player.forward * -length/2)
    bl = player.world_position + (player.right * -width/2) + (player.forward * -length/2)

    # The raycast distances now perfectly match the robot's dimensions.
    if raycast(origin=fl, direction=player.right, distance=width-.2, ignore=(player, floor_ref)).hit: return True
    if raycast(origin=fr, direction=player.forward * -1, distance=length, ignore=(player, floor_ref)).hit: return True
    if raycast(origin=br, direction=player.right * -1, distance=width-.2, ignore=(player, floor_ref)).hit: return True
    if raycast(origin=bl, direction=player.forward, distance=length, ignore=(player, floor_ref)).hit: return True

    return False


def update():
    """Handles player input with realistic acceleration and robust collision."""
    global velocity, rotation_velocity
    
    if whiskers and whiskers[0].enabled:
        width = 1.0
        length = 1.0
        
        y_offset = player.up * 0.8
        
        fr = player.world_position + (player.right * width/2) + (player.forward * length/2) + y_offset
        fl = player.world_position + (player.right * -width/2) + (player.forward * length/2) + y_offset
        br = player.world_position + (player.right * width/2) + (player.forward * -length/2) + y_offset
        bl = player.world_position + (player.right * -width/2) + (player.forward * -length/2) + y_offset
        
        whiskers[0].model.vertices = [fl, fr]
        whiskers[1].model.vertices = [fr, br]
        whiskers[2].model.vertices = [br, bl]
        whiskers[3].model.vertices = [bl, fl]
        whiskers[0].model.generate()
        whiskers[1].model.generate()
        whiskers[2].model.generate()
        whiskers[3].model.generate()

    original_rotation = player.rotation_y
    player.rotation_y += (held_keys['right arrow'] - held_keys['left arrow']) * time.dt * turn_speed
    if check_collision():
        player.rotation_y = original_rotation

    acceleration_direction = (held_keys['up arrow'] - held_keys['down arrow'])
    velocity += player.forward * acceleration_direction * acceleration * time.dt
    
    forward_speed = dot(velocity, player.forward)
    sideways_speed = dot(velocity, player.right)
    
    forward_velocity = player.forward * forward_speed
    sideways_velocity = player.right * sideways_speed
    
    forward_velocity -= forward_velocity * friction * time.dt
    sideways_velocity -= sideways_velocity * (friction * 1.5) * time.dt
    
    velocity = forward_velocity + sideways_velocity

    move_amount = velocity * time.dt
    
    original_x = player.x
    player.x += move_amount.x
    if check_collision():
        player.x = original_x
        velocity.x = 0
            
    original_z = player.z
    player.z += move_amount.z
    if check_collision():
        player.z = original_z
        velocity.z = 0

    ground_check = raycast(player.world_position, (0, -1, 0), distance=robot_height * 0.51, ignore=[player,])
    if not ground_check.hit:
        player.y -= gravity * time.dt
    
    camera_rig.position = player.position
    camera_rig.rotation_y = player.rotation_y

    if top_down_cam.enabled:
        top_down_cam.x = player.x
        top_down_cam.z = player.z
        top_down_cam.y = zoom_level


def update_main_camera_view():
    """Switches between FPV and Chase Cam based on the is_chase_cam flag."""
    if is_chase_cam:
        camera.position = (0, robot_height * 1.5, -1.5)
        player.visible = True
    else:
        camera.position = (0, robot_height, 0)
        player.visible = False

def input(key):
    """Handles single key press events for toggling views."""
    global zoom_level
    global is_chase_cam

    if key == 'tab':
        camera.enabled = not camera.enabled
        top_down_cam.enabled = not top_down_cam.enabled
        player.visible = top_down_cam.enabled or is_chase_cam

    if key == 'v':
        if camera.enabled:
            is_chase_cam = not is_chase_cam
            update_main_camera_view()
    
    if key == 'c':
        if whiskers:
            for w in whiskers:
                w.enabled = not w.enabled

    if top_down_cam.enabled:
        if key == 'scroll up':
            zoom_level -= 2
        if key == 'scroll down':
            zoom_level += 2
        zoom_level = clamp(zoom_level, 5, 50)


if __name__ == '__main__':
    app = Ursina()
    app.development_mode = False
    
    sky_texture = load_texture('sky_texture')
    if sky_texture:
        sky = Sky(texture=sky_texture)
        sky.parent = scene

    textures = {
        'wall': load_texture('wall_texture'),
        'wall_top': load_texture('wall_top_texture'),
        'post': load_texture('post_texture'),
        'floor': load_texture('floor_texture'),
        'robot_body': load_texture('robot_body_texture')
    }

    maze_file = 'maze_3d_data.json'
    player_start_position, maze_grid_size, floor_ref = create_maze_from_json(maze_file, textures)

    turn_speed = 125
    acceleration = 20
    friction = 2.0
    velocity = Vec3(0,0,0)
    
    gravity = 1
    is_chase_cam = False
    whiskers = None

    camera_height = maze_grid_size * 1.8
    zoom_level = camera_height

    if player_start_position:
        robot_height = 0.5 / 2
        robot_texture = textures.get('robot_body')
        robot_color = color.white if robot_texture else color.dark_gray
        
        player = Entity(
            position=player_start_position,
            rotation=(0, 0, 0),
            model='cube',
            scale=(0.8, robot_height, 1.0),
            texture=robot_texture,
            color=robot_color,
            visible=False
        )
        
        camera_rig = Entity(
            position=player.position,
            rotation_y=player.rotation_y
        )
        camera.parent = camera_rig
        camera.position = (0, robot_height, 0)
        
        whiskers = [
            Entity(model=Mesh(mode='line'), color=color.orange, enabled=False),
            Entity(model=Mesh(mode='line'), color=color.orange, enabled=False),
            Entity(model=Mesh(mode='line'), color=color.orange, enabled=False),
            Entity(model=Mesh(mode='line'), color=color.orange, enabled=False),
        ]
        
        top_down_cam = EditorCamera(
            rotation=(90, 0, 0),
            position=(0, camera_height, 0),
            enabled=False
        )
        
    window.title = 'Micromouse 3D Maze Viewer (Tab: Top-Down, V: FPV/Chase, C: Whiskers)'
    window.borderless = False
    window.fullscreen = False
    window.exit_button.visible = False
    window.fps_counter.enabled = False

    app.run()