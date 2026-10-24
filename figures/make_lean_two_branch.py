import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch
from mpl_toolkits.mplot3d import proj3d

rng = np.random.default_rng(7)
fig = plt.figure(figsize=(12.5, 10.2), facecolor="white")
ax = fig.add_axes([0.12, 0.08, 0.76, 0.80], projection="3d")
ax.set_facecolor("white")
ax.set_axis_off()
ax.set_box_aspect((1.15, 0.75, 1.55))
ax.view_init(elev=10, azim=-78)
ax.set_xlim(-0.95, 0.95)
ax.set_ylim(-0.45, 0.45)
ax.set_zlim(0.0, 1.12)

TEAL = "#1B8A8F"
CYAN = "#49B8C9"
BLUE = "#245A9E"
GOLD = "#D59A35"
AMBER = "#E7B75B"
PURPLE = "#7A6FB0"

def trunk(t):
    return (0.035*np.sin(2.3*np.pi*t), 0.025*np.cos(1.7*np.pi*t), 0.035 + 0.455*t)

def left(t):
    s = t
    return (-0.055 - 0.48*(s**0.82), 0.035*np.sin(3.2*np.pi*s) + 0.05*s,
            0.49 + 0.48*s + 0.018*np.sin(2.0*np.pi*s))

def right(t):
    s = t
    return (0.055 + 0.48*(s**0.82), -0.035*np.sin(2.8*np.pi*s) - 0.04*s,
            0.49 + 0.51*s + 0.012*np.cos(2.3*np.pi*s))

def draw_bundle(fn, n, color_a, color_b, t0=0.0, t1=1.0, base_radius=0.06,
                twist=3.0, lw_scale=1.0, alpha=0.80, seed=0):
    rng = np.random.default_rng(seed)
    for i in range(n):
        phase = 2*np.pi*i/n + rng.normal(0, 0.06)
        radius = base_radius*(0.55 + 0.45*rng.random())
        # local perturbation controlled by same t grid
        t = np.linspace(t0, t1, 260)
        bx = np.array([fn(q)[0] for q in t])
        by = np.array([fn(q)[1] for q in t])
        bz = np.array([fn(q)[2] for q in t])
        ang = twist*2*np.pi*t + phase
        # offsets mostly transverse to vertical backbone
        x = bx + radius*(0.75*np.cos(ang) + 0.25*np.cos(phase))*np.sin(np.pi*(t-t0)/(t1-t0+1e-12))**0.7
        y = by + radius*(0.60*np.sin(ang) + 0.25*np.sin(phase))*np.sin(np.pi*(t-t0)/(t1-t0+1e-12))**0.7
        z = bz + 0.010*np.sin(ang + 0.7)
        # color gradient along strand
        c = np.linspace(0, 1, len(t))
        from matplotlib.colors import LinearSegmentedColormap
        cmap = LinearSegmentedColormap.from_list("strand", [color_a, color_b])
        # glow
        ax.plot(x, y, z, color=cmap(0.5), lw=lw_scale*(2.4 + 1.8*rng.random()),
                alpha=0.045, solid_capstyle="round")
        # split line into segments so colour varies along it
        for j in range(0, len(t)-1, 16):
            ax.plot(x[j:j+17], y[j:j+17], z[j:j+17], color=cmap(c[j]),
                    lw=lw_scale*(0.55 + 1.5*rng.random()), alpha=alpha,
                    solid_capstyle="round")

# trunk
draw_bundle(trunk, 34, TEAL, CYAN, base_radius=0.055, twist=2.6, lw_scale=1.15, alpha=0.86, seed=11)
# branches
draw_bundle(left, 30, GOLD, AMBER, t0=0.0, t1=1.0, base_radius=0.075, twist=3.7, lw_scale=1.0, alpha=0.82, seed=21)
draw_bundle(right, 32, BLUE, CYAN, t0=0.0, t1=1.0, base_radius=0.082, twist=2.9, lw_scale=1.05, alpha=0.82, seed=31)

# luminous root
ax.scatter([0.0], [0.0], [0.035], s=260, c="#E8F7F6", edgecolors=CYAN,
           linewidths=2.0, alpha=0.95, depthshade=False)
ax.scatter([0.0], [0.0], [0.035], s=70, c=CYAN, edgecolors="white",
           linewidths=1.0, alpha=1.0, depthshade=False)

# a translucent shared-source ring at the split
theta = np.linspace(0, 2*np.pi, 200)
ring_r = 0.095
ax.plot(ring_r*np.cos(theta), ring_r*np.sin(theta), 0.49 + 0.008*np.sin(3*theta),
        color=TEAL, lw=2.0, alpha=0.55)
ax.plot(ring_r*np.cos(theta), ring_r*np.sin(theta), 0.49 + 0.008*np.sin(3*theta),
        color="white", lw=5.0, alpha=0.10)

fig.canvas.draw()

def fig_xy(x, y, z):
    x2, y2, _ = proj3d.proj_transform(x, y, z, ax.get_proj())
    disp = ax.transData.transform((x2, y2))
    return fig.transFigure.inverted().transform(disp)

def label_box(text, xytext, target, color, ha="left", fontsize=9.2):
    fig.text(xytext[0], xytext[1], text, ha=ha, va="center",
             fontsize=fontsize, color="#1B2430", linespacing=1.35,
             bbox=dict(boxstyle="round,pad=0.45", fc="white", ec=color,
                       lw=1.0, alpha=0.93))
    arrow = FancyArrowPatch(xytext, fig_xy(*target), transform=fig.transFigure,
                            arrowstyle="-|>", mutation_scale=12, lw=1.0,
                            color=color, alpha=0.75,
                            connectionstyle="arc3,rad=0.10")
    fig.add_artist(arrow)

# Title
fig.text(0.5, 0.965, "One generated source, two parallel branches",
         ha="center", va="top", fontsize=17, color="#17202A", fontweight="bold")
fig.text(0.5, 0.935, "Lean dependency schematic: shared source first, then arithmetic and physical interfaces",
         ha="center", va="top", fontsize=10.5, color="#4A5563")

# labels
label_box(
    "MATHEMATICAL BRANCH\n"
    "MathematicalInterface.generated\n"
    "ArithmeticFoundation\n\n"
    "ordered expressions\n"
    "complete histories\n"
    "prime occupation\n"
    "Möbius–Gaussian readout",
    (0.025, 0.53), (-0.47, 0.0, 0.78), GOLD, fontsize=8.8)

label_box(
    "PHYSICAL BRANCH\n"
    "PhysicalInterface\n"
    "SourcePhysicalInterface.generatedCore\n\n"
    "SU(3) × SU(2) × U(1) / Z6\n"
    "16D matter · scalar connector\n"
    "generated YM Hessian / gap\n"
    "Lorentz event carrier",
    (0.700, 0.55), (0.47, 0.0, 0.79), BLUE, fontsize=8.8)

# root
fig.text(0.5, 0.067, "MINIMAL CHANGE\nSource.CanonicalRoot.generated\n↓\nSource.CommonSource.generated",
         ha="center", va="center", fontsize=9.0, color="#1B2430", linespacing=1.35,
         bbox=dict(boxstyle="round,pad=0.45", fc="white", ec=TEAL, lw=1.2, alpha=0.94))

# shared source annotations
fig.text(0.5, 0.405, "SHARED UPSTREAM\nGaussian composition law\nHermite operations · finite-corner algebra\ncentral parity · complete observations",
         ha="center", va="center", fontsize=8.3, color="#1B2430", linespacing=1.3,
         bbox=dict(boxstyle="round,pad=0.38", fc="white", ec=TEAL, lw=0.9, alpha=0.88))

# joint closure at top
fig.text(0.5, 0.885, "JOINT PUBLIC CLOSURE\nCommonFoundation.generated\nCanonicalClosedWorld.generated",
         ha="center", va="center", fontsize=8.6, color="#1B2430", linespacing=1.3,
         bbox=dict(boxstyle="round,pad=0.38", fc="white", ec="#6B7280", lw=0.9, alpha=0.80))
# dotted arcs from branch tips to closure (schematic, not import edges)
for start, rad in [((0.29, 0.865), 0.25), ((0.71, 0.865), -0.25)]:
    fig.add_artist(FancyArrowPatch(start, (0.5, 0.885), transform=fig.transFigure,
                                   arrowstyle="-", mutation_scale=1, lw=0.9,
                                   color="#6B7280", alpha=0.55, linestyle=(0, (3, 3)),
                                   connectionstyle=f"arc3,rad={rad}"))

# footnote
fig.text(0.5, 0.018,
         "Schematic of Lean dependency direction, not a geometric embedding or a claim of equal carrier dimensions. "
         "The arithmetic entry imports no module in Physical; shared proofs remain upstream.",
         ha="center", va="bottom", fontsize=7.4, color="#5B6573")

fig.savefig("figures/lean_source_two_branches.png", dpi=320,
            facecolor="white", bbox_inches="tight", pad_inches=0.08)
fig.savefig("figures/lean_source_two_branches.pdf",
            facecolor="white", bbox_inches="tight", pad_inches=0.08)
print("saved")
