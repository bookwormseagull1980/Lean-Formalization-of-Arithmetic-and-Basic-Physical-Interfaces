import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch, Circle, Polygon
from matplotlib.colors import LinearSegmentedColormap
from mpl_toolkits.mplot3d import proj3d

rng = np.random.default_rng(77)
fig = plt.figure(figsize=(15.2, 9.8), facecolor="white")

TEAL="#147D86"; CYAN="#4CC3D2"; BLUE="#245E9E"; DEEP="#173F73"
GOLD="#C98A2D"; AMBER="#F1C66B"; INK="#16202A"; GREY="#5B6573"

# ---------------- centre: split tree ----------------
ax = fig.add_axes([0.345, 0.115, 0.31, 0.72], projection="3d")
ax.set_axis_off(); ax.set_facecolor("white")
ax.set_box_aspect((1.0,0.7,1.6)); ax.view_init(elev=7, azim=-82)
ax.set_xlim(-0.7,0.7); ax.set_ylim(-0.38,0.38); ax.set_zlim(0,1.02)

def trunk(s): return (0.02*np.sin(2.3*np.pi*s),0.02*np.cos(1.8*np.pi*s),0.035+0.40*s)
def left(s): return (-0.018-0.42*s**0.78,0.055*np.sin(2.0*np.pi*s),0.435+0.46*s)
def right(s): return (0.018+0.44*s**0.80,-0.055*np.sin(1.9*np.pi*s),0.435+0.49*s)

def deriv(fn,t,h=1e-4):
    d=np.array(fn(min(1,t+h)))-np.array(fn(max(0,t-h)))
    n=np.linalg.norm(d); return d/(n if n>1e-12 else 1)
def strand(fn,s,phase,r0,r1,tw,wob,rr):
    p=np.array(fn(s)); t=deriv(fn,s)
    n=np.cross(t,[0,0,1.]); nn=np.linalg.norm(n)
    n=np.array([1,0,0.]) if nn<1e-9 else n/nn
    b=np.cross(t/np.linalg.norm(t),n)
    rad=(r0+(r1-r0)*s**0.75)*(0.6+0.4*rr.random())*np.sin(np.pi*s)**0.35
    ang=tw*np.pi*s+phase+wob*np.sin(2*np.pi*s+phase)
    return (p[0]+rad*(0.9*np.cos(ang)*n[0]+0.7*np.sin(ang)*b[0]),
            p[1]+rad*(0.9*np.cos(ang)*n[1]+0.7*np.sin(ang)*b[1]),
            p[2]+rad*(0.5*np.cos(ang)*n[2]+0.5*np.sin(ang)*b[2]))
def bundle(fn,count,c1,c2,seed,r0,r1,tw):
    rr=np.random.default_rng(seed); cmap=LinearSegmentedColormap.from_list("x",[c1,c2])
    for k in range(4):
        ph=2*np.pi*k/4+0.3*rr.normal(); ts=np.linspace(0,1,300)
        ps=np.array([strand(fn,s,ph,r0*1.1,r1*1.05,tw*0.95,0.6,rr) for s in ts])
        ax.plot(ps[:,0],ps[:,1],ps[:,2],color=c1 if k%2 else c2,lw=6.0,alpha=0.055)
    for i in range(count):
        ph=2*np.pi*i/count+0.5*rr.normal(); twi=tw*(0.75+0.6*rr.random())*(1 if rr.random()>.16 else -1)
        ts=np.linspace(0,1,310); ps=np.array([strand(fn,s,ph,r0*(0.6+.6*rr.random()),r1*(0.6+.7*rr.random()),twi,0.5+.8*rr.random(),rr) for s in ts])
        lw=1.0+2.8*rr.random()**1.5; al=0.48+0.35*rr.random()
        for q in range(0,len(ts)-1,12):
            ax.plot(ps[q:q+13,0],ps[q:q+13,1],ps[q:q+13,2],color=cmap(q/len(ts)),lw=lw,alpha=al,solid_capstyle="round")
bundle(trunk,34,TEAL,CYAN,5,0.018,0.052,3.1)
bundle(left,44,GOLD,AMBER,9,0.022,0.100,3.5)
bundle(right,46,DEEP,CYAN,13,0.022,0.105,3.2)
for z,s in [(0.035,300),(0.438,260)]:
    ax.scatter([0],[0],[z],s=s,c="#EAF9F8",edgecolors=CYAN if z>0.1 else TEAL,linewidths=2,depthshade=False,alpha=.9)
    ax.scatter([0],[0],[z],s=s*.24,c=CYAN if z>0.1 else TEAL,edgecolors="white",linewidths=1,depthshade=False)
fig.canvas.draw()
def fxy(x,y,z):
    x2,y2,_=proj3d.proj_transform(x,y,z,ax.get_proj()); d=ax.transData.transform((x2,y2))
    return fig.transFigure.inverted().transform(d)

fig.text(0.5,0.962,"One generated source, two parallel branches",ha="center",va="top",fontsize=18,color=INK,fontweight="bold")
fig.text(0.5,0.928,"Same Gaussian source and operation algebra upstream; arithmetic and physical interfaces are parallel conclusions",ha="center",va="top",fontsize=10.2,color=GREY)
fig.text(0.5,0.055,"MINIMAL CHANGE\nSource.CanonicalRoot.generated  →  Source.CommonSource.generated",ha="center",va="center",fontsize=8.9,color=INK,linespacing=1.3,
         bbox=dict(boxstyle="round,pad=0.4",fc="white",ec=TEAL,lw=1.1))
fig.text(0.5,0.320,"SHARED UPSTREAM\nGaussian composition law · Hermite operations\nfinite-corner algebra · central parity · complete observations",ha="center",va="center",fontsize=7.8,color=INK,linespacing=1.3,
         bbox=dict(boxstyle="round,pad=0.32",fc="white",ec=TEAL,lw=.9,alpha=.92))
fig.text(0.5,0.845,"JOINT PUBLIC CLOSURE\nCommonFoundation.generated · CanonicalClosedWorld.generated",ha="center",va="center",fontsize=8.0,color=INK,linespacing=1.25,
         bbox=dict(boxstyle="round,pad=0.3",fc="white",ec="#6B7280",lw=.9,alpha=.86))

# ---------------- side panels ----------------
def panel_axes(rect,color,title,names):
    a=fig.add_axes(rect); a.set_xlim(0,1); a.set_ylim(0,1); a.axis("off")
    a.add_patch(FancyBboxPatch((0.005,0.005),0.99,0.99,boxstyle="round,pad=0.012,rounding_size=0.02",
                               transform=a.transAxes,facecolor="white",edgecolor=color,lw=1.5,alpha=.97,clip_on=False))
    a.text(.5,.955,title,ha="center",va="top",fontsize=12.5,color=color,fontweight="bold",transform=a.transAxes)
    a.text(.5,.900,names,ha="center",va="top",fontsize=8.0,color=INK,linespacing=1.28,transform=a.transAxes,
           bbox=dict(boxstyle="round,pad=0.25",fc="#F8FAFB",ec=color,lw=.6,alpha=.8))
    return a

# math panel
am=panel_axes([0.018,0.17,0.292,0.67],GOLD,"MATHEMATICAL BRANCH","MathematicalInterface.generated\nArithmeticFoundation")
# number line
y=.725; am.plot([.10,.90],[y,y],color="#8C6A2F",lw=1.4,transform=am.transAxes)
for n in range(1,10):
    x=.10+.80*(n-1)/8
    am.plot([x,x],[y-.018,y+.018],color="#8C6A2F",lw=.8,transform=am.transAxes)
    am.text(x,y-.052,str(n),ha="center",va="top",fontsize=7.4,color=INK,transform=am.transAxes)
for n in [2,3,5,7]:
    x=.10+.80*(n-1)/8
    am.add_patch(Circle((x,y),.022,transform=am.transAxes,facecolor=AMBER,edgecolor=GOLD,lw=.8,zorder=3))
am.text(.5,.775,"natural numbers · ordered expressions",ha="center",va="bottom",fontsize=7.6,color=GREY,transform=am.transAxes)

# history tree
def node(x,y,label=""):
    am.add_patch(Circle((x,y),.018,transform=am.transAxes,facecolor="white",edgecolor=GOLD,lw=1.0,zorder=4))
    if label: am.text(x,y-.045,label,ha="center",va="top",fontsize=6.5,color=GREY,transform=am.transAxes)
for x1,x2 in [(.50,.34),(.50,.66),(.34,.24),(.34,.44),(.66,.56),(.66,.76)]:
    am.plot([x1,x2],[.555,.485],color="#C8A35A",lw=.9,transform=am.transAxes,zorder=2)
for x in [.50,.34,.66,.24,.44,.56,.76]:
    node(x,.555 if x==.50 else (.485 if x in [.34,.66] else .415))
am.text(.5,.365,"complete ordered histories",ha="center",va="top",fontsize=7.6,color=GREY,transform=am.transAxes)

# prime occupation grid
primes=[2,3,5,7,11,13,17,19]
for ix,p in enumerate(primes):
    for iy in range(4):
        x=.13+.74*ix/7; y=.175+.032*iy
        hit=(iy < (1+ix%4))
        am.add_patch(Circle((x,y),.010,transform=am.transAxes,facecolor=GOLD if hit else "#F4E4C4",edgecolor="#B98A33",lw=.45,zorder=3))
    am.text(x,.135,str(p),ha="center",va="top",fontsize=6.2,color=GREY,transform=am.transAxes)
am.text(.5,.288,"prime occupation · Möbius–Gaussian readout",ha="center",va="bottom",fontsize=7.6,color=GREY,transform=am.transAxes)
am.text(.5,.070,"discrete arithmetic structure, not spacetime",ha="center",va="center",fontsize=7.2,color="#8C6A2F",style="italic",transform=am.transAxes)

# physics panel
ap=panel_axes([0.690,0.17,0.292,0.67],BLUE,"PHYSICAL BRANCH","PhysicalInterface\nSourcePhysicalInterface.generatedCore")
ap.text(.5,.845,"SU(3) × SU(2) × U(1) / Z6",ha="center",va="top",fontsize=8.2,color=BLUE,fontweight="bold",transform=ap.transAxes)

# RP3 sphere inset
asp=fig.add_axes([0.715,0.545,0.160,0.165],projection="3d")
asp.set_axis_off(); asp.set_facecolor("none"); asp.view_init(elev=18,azim=28)
u=np.linspace(0,2*np.pi,40); v=np.linspace(0,np.pi,22)
X=np.outer(np.cos(u),np.sin(v)); Y=np.outer(np.sin(u),np.sin(v)); Z=np.outer(np.ones_like(u),np.cos(v))
asp.plot_wireframe(X,Y,Z,color=CYAN,lw=.45,alpha=.28)
th=np.linspace(0,2*np.pi,200)
asp.plot(np.cos(th),np.sin(th),0*th,color=BLUE,lw=1.2,alpha=.7)
asp.scatter([0,0],[0,0],[1,-1],s=30,c=[GOLD,GOLD],edgecolors="white",depthshade=False)
asp.plot([0,0],[0,0],[1,-1],color=GOLD,lw=1.0,ls=(0,(3,2)),alpha=.8)
ap.text(.5,.535,"RP³ = S³ / Z₂",ha="center",va="top",fontsize=8.6,color=BLUE,fontweight="bold",transform=ap.transAxes)
ap.text(.5,.505,"compact internal 3-geometry",ha="center",va="top",fontsize=7.2,color=GREY,transform=ap.transAxes)

# 16D bars
for i in range(16):
    x=.15+.70*i/15; h=.085+.018*(i%3)
    filled=i<15
    ap.add_patch(FancyBboxPatch((x-.012,.355),.024,h,boxstyle="round,pad=0.002,rounding_size=0.003",
                                transform=ap.transAxes,facecolor=BLUE if filled else "white",edgecolor=BLUE,lw=.8,alpha=.85))
    if not filled:
        ap.text(x,.342,"νR",ha="center",va="top",fontsize=6.0,color=BLUE,transform=ap.transAxes)
ap.text(.5,.330,"16D matter module (complex): 8L + (7R + 1 neutral)",ha="center",va="bottom",fontsize=7.7,color=BLUE,transform=ap.transAxes)
ap.text(.5,.292,"15D charged quotient",ha="center",va="top",fontsize=7.4,color=GREY,transform=ap.transAxes)

# light cone
axc=fig.add_axes([0.735,0.215,0.16,0.090]); axc.set_xlim(-1,1); axc.set_ylim(0,1); axc.axis("off")
axc.add_patch(Polygon([[-.9,.08],[0,.92],[.9,.08]],closed=True,facecolor=CYAN,alpha=.11,edgecolor=CYAN,lw=1.0))
axc.plot([0,0],[.08,.92],color=BLUE,lw=1.0)
axc.annotate("",xy=(0,.98),xytext=(0,.86),arrowprops=dict(arrowstyle="-|>",color=BLUE,lw=1.0))
axc.text(.02,.96,"t",fontsize=7,color=BLUE,va="bottom")
axc.text(-.95,.02,"space",fontsize=6.5,color=GREY)
ap.text(.5,.205,"3+1 Lorentzian event carrier",ha="center",va="top",fontsize=7.8,color=BLUE,fontweight="bold",transform=ap.transAxes)

# ---------------- arrows from panels to branches ----------------
for target,start,color in [((-0.36,0,0.72),(0.305,0.58),GOLD),((0.36,0,0.73),(0.695,0.58),BLUE)]:
    fig.add_artist(FancyArrowPatch(start,fxy(*target),transform=fig.transFigure,arrowstyle="-|>",mutation_scale=11,lw=1.0,color=color,alpha=.75,connectionstyle="arc3,rad=0.06"))

fig.text(0.5,0.012,"Schematic of Lean dependency direction, not a geometric embedding or a claim of equal carrier dimensions. The arithmetic entry imports no module in Physical; shared proofs remain upstream.",
         ha="center",va="bottom",fontsize=7.0,color=GREY)
fig.savefig("figures/lean_source_two_branches_final.png",dpi=340,facecolor="white",bbox_inches="tight",pad_inches=0.06)
fig.savefig("figures/lean_source_two_branches_final.pdf",facecolor="white",bbox_inches="tight",pad_inches=0.06)
print("saved final")
