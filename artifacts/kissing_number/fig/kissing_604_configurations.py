from pathlib import Path

import numpy as np
from plotly.subplots import make_subplots
import plotly.graph_objects as go
from scipy.spatial import ConvexHull
from PIL import Image


HERE = Path(__file__).resolve().parent
DATA = HERE / "kissing_604_figure_data.npz"
OUTPUT_DIR = HERE
PNG = OUTPUT_DIR / "kissing_604_configurations.png"
PDF = OUTPUT_DIR / "kissing_604_configurations.pdf"
RAW_PNG = HERE / ".kissing_604_configurations_raw.png"


def antipodal_segments(points, projected, selected):
    """Return projected antipodal segments, one for each selected line."""
    indices = np.flatnonzero(selected)
    index_set = set(indices.tolist())
    used = set()
    segments = []
    for i in indices:
        if int(i) in used:
            continue
        candidates = np.asarray(sorted(index_set - used - {int(i)}), dtype=int)
        dots = points[candidates] @ points[i]
        j = int(candidates[int(np.argmin(dots))])
        if float(points[j] @ points[i]) > -1.0 + 1e-8:
            raise ValueError("selected extension module is not antipodally paired")
        used.add(int(i))
        used.add(j)
        segments.append((projected[i], projected[j]))
    return segments


def unit_icosphere(subdivisions=2):
    """Return a smooth triangular unit sphere obtained from an icosahedron."""
    golden = (1.0 + np.sqrt(5.0)) / 2.0
    vertices = np.asarray(
        [(0, sy, sz * golden) for sy in (-1, 1) for sz in (-1, 1)]
        + [(sx, sy * golden, 0) for sx in (-1, 1) for sy in (-1, 1)]
        + [(sx * golden, 0, sz) for sx in (-1, 1) for sz in (-1, 1)],
        dtype=float,
    )
    vertices /= np.linalg.norm(vertices, axis=1, keepdims=True)
    faces = ConvexHull(vertices).simplices
    for _ in range(subdivisions):
        vertex_list = vertices.tolist()
        midpoint_cache = {}

        def midpoint(a, b):
            edge = tuple(sorted((int(a), int(b))))
            if edge not in midpoint_cache:
                point = vertices[edge[0]] + vertices[edge[1]]
                point /= np.linalg.norm(point)
                midpoint_cache[edge] = len(vertex_list)
                vertex_list.append(point.tolist())
            return midpoint_cache[edge]

        refined = []
        for a, b, c in faces:
            ab, bc, ca = midpoint(a, b), midpoint(b, c), midpoint(c, a)
            refined.extend([(a, ab, ca), (b, bc, ab), (c, ca, bc), (ab, bc, ca)])
        vertices = np.asarray(vertex_list)
        faces = np.asarray(refined, dtype=int)
    return vertices, faces


SPHERE_VERTICES, SPHERE_FACES = unit_icosphere()


def sphere_mesh(centers, radius):
    """Combine smooth spherical point glyphs centered at the supplied locations."""
    vertices = []
    triangles = []
    for center in centers:
        offset = len(vertices)
        vertices.extend((center + radius * SPHERE_VERTICES).tolist())
        triangles.extend((SPHERE_FACES + offset).tolist())
    return np.asarray(vertices), np.asarray(triangles, dtype=int)


def structural_projection(stiff_pairs, soft):
    """Place stiff coordinate lines around a regular 16-gon; send the soft diagonal vertically."""
    order = [axis for pair in stiff_pairs for axis in pair]
    # Coordinate axes are unoriented lines because both signs occur.  Eight angles
    # in [0, pi) therefore give the eight distinct axes of a regular 16-gon.
    angles = np.pi * np.arange(8) / 8.0
    projection = np.zeros((11, 3), dtype=float)
    projection[order, 0] = np.cos(angles) / 2.0
    projection[order, 1] = np.sin(angles) / 2.0
    projection[soft, 2] = 1.0 / np.sqrt(3.0)
    assert np.allclose(projection.T @ projection, np.eye(3), atol=1e-12)
    return projection


figure_data = np.load(DATA)
shared_stiff_pairs = [(0, 3), (2, 7), (4, 10), (5, 9)]
shared_soft = [1, 6, 8]
configurations = [
    {
        "number": 1,
        "points": figure_data["construction_1"],
        "stiff_pairs": shared_stiff_pairs,
        "soft": shared_soft,
        "core_phase": 1,
        "extension_phase": 1,
    },
    {
        "number": 2,
        "points": figure_data["construction_2"],
        "stiff_pairs": shared_stiff_pairs,
        "soft": shared_soft,
        "core_phase": 1,
        "extension_phase": 2,
    },
    {
        "number": 3,
        "points": figure_data["construction_3"],
        "stiff_pairs": shared_stiff_pairs,
        "soft": shared_soft,
        "core_phase": 2,
        "extension_phase": 2,
    },
]

shared_core_color = "#DDE2E8"
core_phase_colors = {1: "#376FA8", 2: "#D2763F"}
extension_phase_colors = {1: "#8B65A9", 2: "#4F9A78"}


def row_keys(points):
    """Stable keys for exact rows after their common normalization."""
    return [tuple(np.round(row, 12)) for row in points]


# All three are stored in the same coordinate frame.  Constructions 1 and 2 have
# the same 496-point core; Constructions 2 and 3 have the same 108-point extension.  All three share 432
# core points, while the remaining 64 points select one of two core types.
construction_2 = next(config for config in configurations if config["number"] == 2)
construction_3 = next(config for config in configurations if config["number"] == 3)
core_2_keys = set(row_keys(construction_2["points"][:496]))
core_3_keys = set(row_keys(construction_3["points"][:496]))
shared_core_keys = core_2_keys.intersection(core_3_keys)
assert len(shared_core_keys) == 432
assert set(row_keys(configurations[0]["points"][:496])) == core_2_keys
assert set(row_keys(construction_2["points"][496:])) == set(row_keys(construction_3["points"][496:]))

fig = make_subplots(
    rows=1,
    cols=3,
    specs=[[{"type": "scene"}, {"type": "scene"}, {"type": "scene"}]],
    horizontal_spacing=0.005,
)

all_projected = []
for column, config in enumerate(configurations, start=1):
    points = config["points"]
    projection = structural_projection(config["stiff_pairs"], config["soft"])
    projected = points @ projection
    all_projected.append(projected)
    core = np.arange(len(points)) < 496
    common_core = np.asarray(
        [index < 496 and key in shared_core_keys for index, key in enumerate(row_keys(points))]
    )
    phase_core = core & ~common_core
    extension = np.arange(len(points)) >= 496
    assert int(common_core.sum()) == 432
    assert int(phase_core.sum()) == 64
    assert int(extension.sum()) == 108

    # A shaded bounding sphere gives the static image the same depth cue as a
    # molecular rendering.  Orthogonal shadows of unit vectors lie inside it.
    longitude = np.linspace(0, 2.0 * np.pi, 45)
    latitude = np.linspace(0, np.pi, 25)
    sphere_x = np.outer(np.cos(longitude), np.sin(latitude))
    sphere_y = np.outer(np.sin(longitude), np.sin(latitude))
    sphere_z = np.outer(np.ones_like(longitude), np.cos(latitude))
    sphere_tint = 0.55 * sphere_z + 0.30 * sphere_x + 0.15 * sphere_y
    fig.add_trace(
        go.Surface(
            x=sphere_x,
            y=sphere_y,
            z=sphere_z,
            surfacecolor=sphere_tint,
            colorscale=[[0.0, "#C9D3E1"], [0.48, "#EEF2F7"], [1.0, "#FFFFFF"]],
            cmin=-1,
            cmax=1,
            opacity=0.13,
            showscale=False,
            hoverinfo="skip",
            lighting={"ambient": 0.44, "diffuse": 0.78, "specular": 0.55, "roughness": 0.66, "fresnel": 0.18},
            lightposition={"x": 120, "y": 160, "z": 220},
            showlegend=False,
        ),
        row=1,
        col=column,
    )

    # Latitude-longitude curves make the bounding sphere legible in a static view.
    sphere_line_x, sphere_line_y, sphere_line_z = [], [], []
    circle_parameter = np.linspace(0, 2.0 * np.pi, 121)
    for latitude_angle in np.deg2rad([-60, -30, 0, 30, 60]):
        radius_at_latitude = np.cos(latitude_angle)
        sphere_line_x.extend((radius_at_latitude * np.cos(circle_parameter)).tolist() + [None])
        sphere_line_y.extend((radius_at_latitude * np.sin(circle_parameter)).tolist() + [None])
        sphere_line_z.extend((np.full_like(circle_parameter, np.sin(latitude_angle))).tolist() + [None])
    meridian_parameter = np.linspace(-0.5 * np.pi, 0.5 * np.pi, 121)
    for longitude_angle in np.deg2rad(np.arange(0, 180, 30)):
        sphere_line_x.extend((np.cos(meridian_parameter) * np.cos(longitude_angle)).tolist() + [None])
        sphere_line_y.extend((np.cos(meridian_parameter) * np.sin(longitude_angle)).tolist() + [None])
        sphere_line_z.extend(np.sin(meridian_parameter).tolist() + [None])
    fig.add_trace(
        go.Scatter3d(
            x=sphere_line_x, y=sphere_line_y, z=sphere_line_z,
            mode="lines",
            line={"color": "rgba(90,108,132,0.58)", "width": 2.0},
            showlegend=False, hoverinfo="skip",
        ),
        row=1,
        col=column,
    )

    # Coordinate axes start at the origin.  Negative halves are subdued, while
    # positive halves and their labels remain visually prominent.
    axis_specs = [
        ("x", np.array([1.0, 0.0, 0.0]), "#D7443E"),
        ("y", np.array([0.0, 1.0, 0.0]), "#2A9D68"),
        ("z", np.array([0.0, 0.0, 1.0]), "#3478D4"),
    ]
    for axis_name, direction, axis_color in axis_specs:
        negative = -0.94 * direction
        positive = 0.94 * direction
        fig.add_trace(
            go.Scatter3d(
                x=[negative[0], 0, positive[0]],
                y=[negative[1], 0, positive[1]],
                z=[negative[2], 0, positive[2]],
                mode="lines+text",
                text=["", "", axis_name],
                textposition="top center",
                textfont={"size": 18, "color": axis_color},
                line={"color": axis_color, "width": 5},
                opacity=0.58,
                showlegend=False,
                hoverinfo="skip",
            ),
            row=1,
            col=column,
        )
    fig.add_trace(
        go.Scatter3d(
            x=[0], y=[0], z=[0], mode="markers",
            marker={"size": 4.8, "color": "#20242A", "opacity": 1.0},
            showlegend=False, hovertemplate="origin<extra></extra>",
        ),
        row=1,
        col=column,
    )

    mesh_vertices, mesh_faces = sphere_mesh(projected[common_core], radius=0.027)
    fig.add_trace(
        go.Mesh3d(
            x=mesh_vertices[:, 0], y=mesh_vertices[:, 1], z=mesh_vertices[:, 2],
            i=mesh_faces[:, 0], j=mesh_faces[:, 1], k=mesh_faces[:, 2],
            name="432-point shared core",
            legendgroup="shared-core",
            legendrank=0,
            showlegend=column == 1,
            color=shared_core_color,
            opacity=0.62,
            flatshading=False,
            lighting={"ambient": 0.46, "diffuse": 0.80, "specular": 0.62, "roughness": 0.42, "fresnel": 0.12},
            lightposition={"x": 120, "y": 160, "z": 220},
            hovertemplate="point in the shared 432-point core<extra></extra>",
        ),
        row=1,
        col=column,
    )
    core_phase = config["core_phase"]
    mesh_vertices, mesh_faces = sphere_mesh(projected[phase_core], radius=0.031)
    fig.add_trace(
        go.Mesh3d(
            x=mesh_vertices[:, 0], y=mesh_vertices[:, 1], z=mesh_vertices[:, 2],
            i=mesh_faces[:, 0], j=mesh_faces[:, 1], k=mesh_faces[:, 2],
            name=f"64-point core type {['', 'I', 'II'][core_phase]}",
            legendgroup=f"core-phase-{core_phase}",
            legendrank=core_phase,
            showlegend=(config["number"] == 1 if core_phase == 1 else config["number"] == 3),
            color=core_phase_colors[core_phase],
            opacity=0.98,
            flatshading=False,
            lighting={"ambient": 0.30, "diffuse": 0.88, "specular": 0.88, "roughness": 0.28, "fresnel": 0.16},
            lightposition={"x": 120, "y": 160, "z": 220},
            hovertemplate=f"64-point core type {core_phase}<extra></extra>",
        ),
        row=1,
        col=column,
    )

    extension_phase = config["extension_phase"]
    extension_color = extension_phase_colors[extension_phase]
    segments = antipodal_segments(points, projected, extension)
    line_x, line_y, line_z = [], [], []
    for start, end in segments:
        line_x.extend([start[0], 0.0, end[0], None])
        line_y.extend([start[1], 0.0, end[1], None])
        line_z.extend([start[2], 0.0, end[2], None])
    fig.add_trace(
        go.Scatter3d(
            x=line_x, y=line_y, z=line_z,
            mode="lines",
            name=f"extension type {['', 'I', 'II'][extension_phase]} lines",
            legendgroup=f"extension-phase-{extension_phase}",
            showlegend=False,
            line={"color": extension_color, "width": 1.8},
            opacity=0.18,
            hoverinfo="skip",
        ),
        row=1,
        col=column,
    )
    mesh_vertices, mesh_faces = sphere_mesh(projected[extension], radius=0.031)
    fig.add_trace(
        go.Mesh3d(
            x=mesh_vertices[:, 0], y=mesh_vertices[:, 1], z=mesh_vertices[:, 2],
            i=mesh_faces[:, 0], j=mesh_faces[:, 1], k=mesh_faces[:, 2],
            name=f"108-point extension type {['', 'I', 'II'][extension_phase]}",
            legendgroup=f"extension-phase-{extension_phase}",
            legendrank=2 + extension_phase,
            showlegend=(config["number"] == 1 if extension_phase == 1 else config["number"] == 2),
            color=extension_color,
            opacity=0.96,
            flatshading=False,
            lighting={"ambient": 0.30, "diffuse": 0.88, "specular": 0.88, "roughness": 0.28, "fresnel": 0.16},
            lightposition={"x": 120, "y": 160, "z": 220},
            hovertemplate=f"108-point extension type {extension_phase}<extra></extra>",
        ),
        row=1,
        col=column,
    )

axis_style = {
    "range": [-1.04, 1.04],
    "showbackground": False,
    "showgrid": False,
    "zeroline": False,
    "showline": False,
    "showticklabels": False,
    "title": "",
}
camera = {
    "eye": {"x": 0.92, "y": 0.98, "z": 0.66},
    "center": {"x": 0, "y": 0, "z": 0},
    "up": {"x": 0, "y": 0, "z": 1},
    "projection": {"type": "perspective"},
}
for scene_name in ("scene", "scene2", "scene3"):
    fig.layout[scene_name].update(
        xaxis=axis_style,
        yaxis=axis_style,
        zaxis=axis_style,
        aspectmode="cube",
        camera=camera,
    )
    fig.layout[scene_name].domain.y = [0.20, 1.0]

fig.update_layout(
    width=1800,
    height=570,
    margin={"l": 4, "r": 4, "t": 4, "b": 8},
    paper_bgcolor="white",
    plot_bgcolor="white",
    font={"family": "Arial, sans-serif", "color": "#24282F"},
    legend={
        "orientation": "h",
        "x": 0.5,
        "xanchor": "center",
        "y": 0.058,
        "yanchor": "bottom",
        "bgcolor": "rgba(255,255,255,0)",
        "font": {"size": 18},
    },
)

roman = {1: "I", 2: "II"}
for index, config in enumerate(configurations):
    fig.add_annotation(
        x=(index + 0.5) / 3.0,
        y=0.255,
        xref="paper",
        yref="paper",
        text=(
            f"<b>({chr(97 + index)}) Construction {config['number']}</b>"
            f"<br>Core type {roman[config['core_phase']]} + extension type {roman[config['extension_phase']]}"
        ),
        showarrow=False,
        align="center",
        xanchor="center",
        yanchor="top",
        font={"size": 20, "color": "#24282F"},
    )

OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
# PDF is the publication asset. Plotly keeps annotations and legend labels as
# selectable text; its WebGL-rendered three-dimensional meshes are embedded as
# raster layers because Plotly cannot represent those shaded scenes as vector
# PDF primitives.
# Match the compact aspect ratio of the packed PNG.  On the original 1800-pixel
# canvas, each square 3D scene is height-limited and wide blank columns remain;
# narrowing the PDF canvas makes the spheres fill their panels at the same scale
# as the publication PNG while retaining selectable annotation and legend text.
fig.write_image(PDF, format="pdf", width=1360, height=570, scale=1.0)
fig.write_image(RAW_PNG, width=1800, height=570, scale=2.0)

# Plotly assigns each 3D scene one third of the full canvas.  The rendered
# spheres do not fill those scene canvases horizontally, so exporting the raw
# figure leaves wide blank columns.  Crop the three already-rendered panels
# without rescaling them, then repack them with a narrow journal-style gutter.
raw_image = Image.open(RAW_PNG).convert("RGB")
pixels = np.asarray(raw_image)
height, width = pixels.shape[:2]
panel_limit_y = int(0.83 * height)
panel_boxes = []
for panel_index in range(3):
    third_left = panel_index * width // 3
    third_right = (panel_index + 1) * width // 3
    block = pixels[:panel_limit_y, third_left:third_right]
    ink = np.any(block < 245, axis=2)
    ys, xs = np.where(ink)
    panel_boxes.append(
        (
            max(0, third_left + int(xs.min()) - 16),
            max(0, int(ys.min()) - 16),
            min(width, third_left + int(xs.max()) + 17),
            min(panel_limit_y, int(ys.max()) + 17),
        )
    )

common_top = min(box[1] for box in panel_boxes)
common_bottom = max(box[3] for box in panel_boxes)
panel_crops = [raw_image.crop((box[0], common_top, box[2], common_bottom)) for box in panel_boxes]
cell_width = max(crop.width for crop in panel_crops)
gutter = 18

legend_block = pixels[panel_limit_y:]
legend_ink = np.any(legend_block < 245, axis=2)
legend_ys, legend_xs = np.where(legend_ink)
legend_box = (
    max(0, int(legend_xs.min()) - 10),
    max(0, panel_limit_y + int(legend_ys.min()) - 8),
    min(width, int(legend_xs.max()) + 11),
    min(height, panel_limit_y + int(legend_ys.max()) + 9),
)
legend_crop = raw_image.crop(legend_box)

packed_width = 3 * cell_width + 2 * gutter
legend_gap = 10
packed_height = panel_crops[0].height + legend_gap + legend_crop.height + 10
packed = Image.new("RGB", (packed_width, packed_height), "white")
for panel_index, crop in enumerate(panel_crops):
    x = panel_index * (cell_width + gutter) + (cell_width - crop.width) // 2
    packed.paste(crop, (x, 0))
packed.paste(legend_crop, ((packed_width - legend_crop.width) // 2, panel_crops[0].height + legend_gap))
packed.save(PNG, dpi=(300, 300))
RAW_PNG.unlink()
print(PDF)
print(PNG)
