import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch
from matplotlib.colors import LinearSegmentedColormap
from mpl_toolkits.mplot3d import proj3d

rng = np.random.default_rng(41)
fig = plt.figure(figsize=(12.4, 10.2), facecolor="white")
ax = fig.add_axes([0.17, 0.10, 0.66, 0.75], projection="3d")
ax.set_facecolor("white"); ax.set_axis_off()
ax.set_box_aspect((1.35, 0.78, 1.65))
ax.view_init(elev=7, azim=-82)
ax.set_xlim(-0.85, 0.85); ax.set_ylim(-0.42, 0.42); ax.set_zlim(0.0, 1.02)

TEAL="#147D86"; CYAN="#56C7D4"; BLUE="#245E9E"; DEEPBLUE="#173F73"
GOLD="#C98A2D"; AMBER="#F1C66B"; CREAM="#F7E7C4"; INK="#16202A"

def trunk(s):
    return (0.020*np.sin(2.4*np.pi*s), 0.020*np.cos(1.9*np.pi*s), 0.035+0.405*s)
def left(s):
    return (-0.020-0.44*(s**0.78)-0.035*np.sin(np.pi*s),
            0.075*np.sin(2.0*np.pi*s)-0.020*s,
            0.438+0.465*s+0.020*np.sin(2.2*np.pi*s))
def right(s):
    return (0.020+0.46*(s**0.80)+0.035*np.sin(np.pi*s),
            -0.075*np.sin(1.8*np.pi*s)+0.020*s,
            0.438+0.495*s+0.015*np.cos(2.4*np.pi*s))

def strand(fn, s, phase, rad0, rad1, twist, wobble, rng):
    p = np.array(fn(s))
    # local perpendicular frame using a fixed z reference
    h=1e-4
    t = np.array(fn(min(1,s+h)))-np.array(fn(max(0,s-h)))
    n = np.cross(t, np.array([0.,0.,1.])); nn=np.linalg.norm(n)
    if nn < 1e-9: n=np.array([1.,0.,0.])
    else: n=n/nn
    b = np.cross(t/np.linalg.norm(t), n)
    rad = (rad0 + (rad1-rad0)*(s**0.75))*(0.60+0.40*rng.random())
    env = np.sin(np.pi*s)**0.35
    angle = twist*np.pi*s + phase + wobble*np.sin(2.0*np.pi*s+phase)
    x = p[0] + env*rad*(0.92*np.cos(angle)*n[0] + 0.68*np.sin(angle)*b[0])
    y = p[1] + env*rad*(0.92*np.cos(angle)*n[1] + 0.68*np.sin(angle)*b[1])
    z = p[2] + env*rad*(0.55*np.cos(angle)*n[2] + 0.55*np.sin(angle)*b[2])
    return x,y,z

def bundle(fn, count, c1, c2, seed, rad0, rad1, twist_base=3.0):
    r = np.random.default_rng(seed)
    cmap = LinearSegmentedColormap.from_list("c", [c1,c2])
    # underglow ribbons
    for k in range(5):
        phase = 2*np.pi*k/5 + 0.25*r.normal()
        ts = np.linspace(0,1,420)
        xs=[];ys=[];zs=[]
        for s in ts:
            x,y,z = strand(fn,s,phase,rad0*1.15,rad1*1.05,twist_base*0.95,0.6,r)
            xs.append(x); ys.append(y); zs.append(z)
        ax.plot(xs,ys,zs,color=c1 if k%2 else c2,lw=7.5,alpha=0.055,solid_capstyle="round")
    for i in range(count):
        phase = 2*np.pi*i/count + 0.55*r.normal()
        rad0i = rad0*(0.55+0.7*r.random())
        rad1i = rad1*(0.55+0.8*r.random())
        tw = twist_base*(0.75+0.7*r.random()) * (1 if r.random()>0.16 else -1)
        wob = 0.45+0.9*r.random()
        ts = np.linspace(0,1,340)
        pts = np.array([strand(fn,s,phase,rad0i,rad1i,tw,wob,r) for s in ts])
        lw = 1.1 + 3.4*(r.random()**1.7)
        alpha = 0.48 + 0.40*r.random()
        for q in range(0,len(ts)-1,10):
            ax.plot(pts[q:q+11,0],pts[q:q+11,1],pts[q:q+11,2],
                    color=cmap(q/len(ts)), lw=lw, alpha=alpha, solid_capstyle="round")

bundle(trunk, 48, TEAL, CYAN, 5, 0.020, 0.060, twist_base=3.1)
bundle(left, 62, GOLD, AMBER, 9, 0.025, 0.125, twist_base=3.7)
bundle(right, 66, DEEPBLUE, CYAN, 13, 0.025, 0.135, twist_base=3.3)

# connecting wisps around split
for k in range(8):
    ph = 2*np.pi*k/8
    ts=np.linspace(0,1,80)
    x = 0.055*np.cos(ph)*np.sin(np.pi*ts); y=0.045*np.sin(ph)*np.sin(np.pi*ts)
    z=0.405+0.070*ts
    ax.plot(x+0.01*np.cos(ph),y+0.01*np.sin(ph),z,color=CYAN,lw=1.2,alpha=0.35)

# luminous nodes
ax.scatter([0],[0],[0.035],s=300,c="#EAF9F8",edgecolors=TEAL,linewidths=2.2,depthshade=False,alpha=0.95)
ax.scatter([0],[0],[0.035],s=80,c=TEAL,edgecolors="white",linewidths=1.0,depthshade=False)
ax.scatter([0],[0],[0.438],s=260,c="#EAF9F8",edgecolors=CYAN,linewidths=2.0,depthshade=False,alpha=0.9)
ax.scatter([0],[0],[0.438],s=65,c=CYAN,edgecolors="white",linewidths=1.0,depthshade=False)

fig.canvas.draw()
def fxy(x,y,z):
    x2,y2,_=proj3d.proj_transform(x,y,z,ax.get_proj())
    d=ax.transData.transform((x2,y2))
    return fig.transFigure.inverted().transform(d)
def callout(text,xytext,target,color,fs=8.5,ha="left"):
    fig.text(xytext[0],xytext[1],text,ha=ha,va="center",fontsize=fs,color=INK,
             linespacing=1.38,bbox=dict(boxstyle="round,pad=0.42",fc="white",ec=color,lw=1.1,alpha=0.95))
    fig.add_artist(FancyArrowPatch(xytext,fxy(*target),transform=fig.transFigure,
        arrowstyle="-|>",mutation_scale=11,lw=1.0,color=color,alpha=0.8,
        connectionstyle="arc3,rad=0.07"))

fig.text(0.5,0.965,"One generated source, two parallel branches",ha="center",va="top",fontsize=17,color=INK,fontweight="bold")
fig.text(0.5,0.928,"Lean dependency schematic: common source upstream, arithmetic and physical interfaces in parallel",ha="center",va="top",fontsize=10,color="#53606E")

callout("MATHEMATICAL BRANCH\nMathematicalInterface.generated\nArithmeticFoundation\n\nordered expressions · complete histories\nprime occupation · Möbius–Gaussian readout",
        (0.012,0.56),(-0.40,0.0,0.76),GOLD,fs=8.5)
callout("PHYSICAL BRANCH\nPhysicalInterface\nSourcePhysicalInterface.generatedCore\n\nSU(3) × SU(2) × U(1) / Z6\n16D matter · scalar connector\ngenerated YM Hessian / gap · Lorentz carrier",
        (0.690,0.580),(0.40,0.0,0.77),BLUE,fs=8.5)

fig.text(0.5,0.060,"MINIMAL CHANGE\nSource.CanonicalRoot.generated\n↓\nSource.CommonSource.generated",
         ha="center",va="center",fontsize=9.0,color=INK,linespacing=1.35,
         bbox=dict(boxstyle="round,pad=0.45",fc="white",ec=TEAL,lw=1.2,alpha=0.95))
fig.text(0.5,0.312,"SHARED UPSTREAM\nGaussian composition law\nHermite operations · finite-corner algebra\ncentral parity · complete observations",
         ha="center",va="center",fontsize=8.0,color=INK,linespacing=1.28,
         bbox=dict(boxstyle="round,pad=0.35",fc="white",ec=TEAL,lw=0.95,alpha=0.90))
fig.text(0.5,0.858,"JOINT PUBLIC CLOSURE\nCommonFoundation.generated · CanonicalClosedWorld.generated",
         ha="center",va="center",fontsize=8.2,color=INK,linespacing=1.25,
         bbox=dict(boxstyle="round,pad=0.35",fc="white",ec="#6B7280",lw=0.9,alpha=0.84))
fig.text(0.5,0.013,"Schematic of Lean dependency direction, not a geometric embedding or a claim of equal carrier dimensions. The arithmetic entry imports no module in Physical; shared proofs remain upstream.",
         ha="center",va="bottom",fontsize=7.0,color="#5B6573")

fig.savefig("figures/lean_source_two_branches_v3.png",dpi=340,facecolor="white",bbox_inches="tight",pad_inches=0.06)
fig.savefig("figures/lean_source_two_branches_v3.pdf",facecolor="white",bbox_inches="tight",pad_inches=0.06)
print("saved v3")
