import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch
from matplotlib.colors import LinearSegmentedColormap
from mpl_toolkits.mplot3d import proj3d

rng = np.random.default_rng(19)
fig = plt.figure(figsize=(12.6, 10.4), facecolor="white")
ax = fig.add_axes([0.15, 0.10, 0.70, 0.74], projection="3d")
ax.set_facecolor("white")
ax.set_axis_off()
ax.set_box_aspect((1.25, 0.72, 1.65))
ax.view_init(elev=8, azim=-80)
ax.set_xlim(-0.95, 0.95)
ax.set_ylim(-0.42, 0.42)
ax.set_zlim(0.0, 1.05)

TEAL = "#177E86"
CYAN = "#4CC3D2"
BLUE = "#225C9C"
GOLD = "#C98B2E"
AMBER = "#F0C36A"
INK = "#17202A"

def trunk(t):
    return (0.030*np.sin(2.2*np.pi*t), 0.025*np.cos(1.8*np.pi*t), 0.030 + 0.405*t)

def left(t):
    s = t
    return (-0.045 - 0.50*(s**0.78), 0.060*np.sin(3.0*np.pi*s) + 0.045*s,
            0.435 + 0.475*s + 0.020*np.sin(2.1*np.pi*s))

def right(t):
    s = t
    return (0.045 + 0.52*(s**0.80), -0.060*np.sin(2.7*np.pi*s) - 0.035*s,
            0.435 + 0.505*s + 0.015*np.cos(2.4*np.pi*s))

def deriv(fn, t, h=1e-4):
    a = np.array(fn(max(0, t-h))); b = np.array(fn(min(1, t+h)))
    d = b-a
    n = np.linalg.norm(d)
    return d/(n if n > 1e-12 else 1.0)

def tube(fn, t0, t1, radius, color, phase=0.0, offset=(0,0,0), n_t=170, n_s=15, alpha=0.92):
    ts = np.linspace(t0, t1, n_t)
    pts = np.array([fn(t) for t in ts]) + np.array(offset)
    # local frame
    tangents = np.array([deriv(fn, t) for t in ts])
    ref = np.array([0.0, 0.0, 1.0])
    normals = np.cross(tangents, ref)
    norms = np.linalg.norm(normals, axis=1)
    norms[norms < 1e-9] = 1.0
    normals = normals / norms[:, None]
    binormals = np.cross(tangents, normals)
    ss = np.linspace(0, 2*np.pi, n_s, endpoint=True)
    # taper at ends
    taper = np.sin(np.pi*(ts-ts[0])/(ts[-1]-ts[0]))**0.35
    radii = radius*taper
    verts = np.empty((n_t, n_s, 3))
    for i in range(n_t):
        verts[i] = pts[i] + radii[i]*(np.cos(ss+phase)[:,None]*normals[i] + np.sin(ss+phase)[:,None]*binormals[i])
    X = verts[:,:,0]; Y = verts[:,:,1]; Z = verts[:,:,2]
    cmap = LinearSegmentedColormap.from_list("tube", [color, "#FFFFFF"])
    # shade by z and angle
    fc = np.empty((n_t-1, n_s-1, 4))
    base = np.array(matplotlib.colors.to_rgba(color))
    for i in range(n_t-1):
        shade = 0.55 + 0.40*(i/(n_t-1))
        fc[i,:,0] = base[0]*shade + (1-shade)*0.95
        fc[i,:,1] = base[1]*shade + (1-shade)*0.95
        fc[i,:,2] = base[2]*shade + (1-shade)*0.95
        fc[i,:,3] = alpha
    ax.plot_surface(X, Y, Z, facecolors=fc, rstride=3, cstride=2,
                    linewidth=0, antialiased=True, shade=False, zorder=1)

def bundle(fn, tubes, filaments, color_a, color_b, seed, t0=0.0, t1=1.0):
    r = np.random.default_rng(seed)
    for k in range(tubes):
        ph = 2*np.pi*k/tubes + 0.25*r.normal()
        off = (0.030*np.cos(ph), 0.025*np.sin(ph), 0.0)
        tube(fn, t0, t1, 0.018 + 0.010*r.random(), color_a if k%2 else color_b,
             phase=ph, offset=off, alpha=0.80)
    for j in range(filaments):
        ph = 2*np.pi*j/filaments + 0.3*r.normal()
        rad = 0.060*(0.55+0.45*r.random())
        ts = np.linspace(t0, t1, 260)
        pts = np.array([fn(t) for t in ts])
        tang = np.array([deriv(fn, t) for t in ts])
        ref = np.array([0.0,0.0,1.0])
        nor = np.cross(tang, ref); nor /= np.maximum(np.linalg.norm(nor,axis=1)[:,None],1e-9)
        bin = np.cross(tang, nor)
        ang = 3.1*2*np.pi*ts + ph
        taper = np.sin(np.pi*(ts-ts[0])/(ts[-1]-ts[0]))**0.7
        x = pts[:,0] + (rad*taper)*(np.cos(ang)*nor[:,0] + np.sin(ang)*bin[:,0])
        y = pts[:,1] + (rad*taper)*(np.cos(ang)*nor[:,1] + np.sin(ang)*bin[:,1])
        z = pts[:,2] + (0.012*taper)*np.sin(ang+0.4)
        cmap = LinearSegmentedColormap.from_list("fil", [color_a, color_b])
        for q in range(0, len(ts)-1, 12):
            ax.plot(x[q:q+13], y[q:q+13], z[q:q+13], color=cmap(q/len(ts)),
                    lw=0.8 + 1.9*r.random(), alpha=0.60, solid_capstyle="round")

bundle(trunk, 4, 22, TEAL, CYAN, seed=3)
bundle(left, 5, 18, GOLD, AMBER, seed=7)
bundle(right, 5, 20, BLUE, CYAN, seed=11)

# luminous split node
ax.scatter([0.0],[0.0],[0.435], s=320, c="#E9F9F8", edgecolors=CYAN, linewidths=2.0, depthshade=False, alpha=0.95)
ax.scatter([0.0],[0.0],[0.435], s=90, c=CYAN, edgecolors="white", linewidths=1.0, depthshade=False)
# root node
ax.scatter([0.0],[0.0],[0.030], s=260, c="#E9F9F8", edgecolors=TEAL, linewidths=2.0, depthshade=False)
ax.scatter([0.0],[0.0],[0.030], s=70, c=TEAL, edgecolors="white", linewidths=1.0, depthshade=False)

fig.canvas.draw()
def fxy(x,y,z):
    x2,y2,_ = proj3d.proj_transform(x,y,z,ax.get_proj())
    d = ax.transData.transform((x2,y2))
    return fig.transFigure.inverted().transform(d)

def callout(text, xytext, target, color, ha="left", fs=8.8):
    fig.text(xytext[0], xytext[1], text, ha=ha, va="center", fontsize=fs,
             color=INK, linespacing=1.38,
             bbox=dict(boxstyle="round,pad=0.42", fc="white", ec=color, lw=1.1, alpha=0.95))
    fig.add_artist(FancyArrowPatch(xytext, fxy(*target), transform=fig.transFigure,
        arrowstyle="-|>", mutation_scale=11, lw=1.0, color=color, alpha=0.8,
        connectionstyle="arc3,rad=0.08"))

fig.text(0.5, 0.965, "One generated source, two parallel branches", ha="center", va="top",
         fontsize=17, color=INK, fontweight="bold")
fig.text(0.5, 0.928, "Lean dependency schematic: common source upstream, arithmetic and physical interfaces in parallel",
         ha="center", va="top", fontsize=10, color="#53606E")

callout("MATHEMATICAL BRANCH\nMathematicalInterface.generated\nArithmeticFoundation\n\nordered expressions\ncomplete histories\nprime occupation\nMöbius–Gaussian readout",
        (0.015, 0.56), (-0.44, 0.0, 0.76), GOLD, fs=8.5)
callout("PHYSICAL BRANCH\nPhysicalInterface\nSourcePhysicalInterface.generatedCore\n\nSU(3) × SU(2) × U(1) / Z6\n16D matter · scalar connector\ngenerated YM Hessian / gap\nLorentz event carrier",
        (0.715, 0.58), (0.44, 0.0, 0.77), BLUE, fs=8.5)

fig.text(0.5, 0.065,
         "MINIMAL CHANGE\nSource.CanonicalRoot.generated\n↓\nSource.CommonSource.generated",
         ha="center", va="center", fontsize=9.0, color=INK, linespacing=1.35,
         bbox=dict(boxstyle="round,pad=0.45", fc="white", ec=TEAL, lw=1.2, alpha=0.95))

fig.text(0.5, 0.335,
         "SHARED UPSTREAM\nGaussian composition law\nHermite operations · finite-corner algebra\ncentral parity · complete observations",
         ha="center", va="center", fontsize=8.1, color=INK, linespacing=1.28,
         bbox=dict(boxstyle="round,pad=0.35", fc="white", ec=TEAL, lw=0.95, alpha=0.90))

fig.text(0.5, 0.865,
         "JOINT PUBLIC CLOSURE\nCommonFoundation.generated · CanonicalClosedWorld.generated",
         ha="center", va="center", fontsize=8.4, color=INK, linespacing=1.25,
         bbox=dict(boxstyle="round,pad=0.35", fc="white", ec="#6B7280", lw=0.9, alpha=0.82))

fig.text(0.5, 0.015,
         "Schematic of Lean dependency direction, not a geometric embedding or a claim of equal carrier dimensions. The arithmetic entry imports no module in Physical; shared proofs remain upstream.",
         ha="center", va="bottom", fontsize=7.1, color="#5B6573")

fig.savefig("figures/lean_source_two_branches_v2.png", dpi=340, facecolor="white", bbox_inches="tight", pad_inches=0.06)
fig.savefig("figures/lean_source_two_branches_v2.pdf", facecolor="white", bbox_inches="tight", pad_inches=0.06)
print("saved v2")
