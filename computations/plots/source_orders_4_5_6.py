"""Source plot for the order-four through order-six numerical arrays.

Used by make_print_figures.py; output is captured before serialization.
"""

if not __debug__:
    raise RuntimeError("Exact verification requires Python without -O or -OO.")

from pathlib import Path
from decimal import Decimal, localcontext
from fractions import Fraction as F
import json, sys

sys.set_int_max_str_digits(0)
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

R = Path(__file__).resolve().parent.parent
H = R / "hierarchical"
plt.rcParams.update(
    {
        "font.size": 10,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "pdf.fonttype": 42,
    }
)
fig, axs = plt.subplots(
    2, 3, figsize=(13.2, 7.2), gridspec_kw={"height_ratios": [1.35, 1]}
)
for col, k in enumerate([4, 5, 6]):
    d = json.loads((H / f"order{k}_recursive_replay.json").read_text())
    p = (
        json.loads((H / "order6_dense_certified_samples.json").read_text())["samples"]
        if k == 6
        else d["samples"]
    )
    cons = json.loads((R / f"order{k}_construction.json").read_text())
    cp = F(cons["rate_constant_power_k"])
    D = int(d["integer_scale"])
    norm = F(int(d["normalization_max_scaled"]), D)
    with localcontext() as ctx:
        ctx.prec = 85
        dc = lambda f: Decimal(f.numerator) / Decimal(f.denominator)
        logc = float(dc(cp).log10() / k - dc(norm).log10())
    p = p[2:]
    x = [float(z["log10_t"]) for z in p]
    y = [float(z["log10_normalized_gap"]) for z in p]
    ax = axs[0, col]
    ax.plot(
        x, y, "o-", color="#1261a0", ms=4, lw=1.7, label="Certified boundary samples"
    )
    ax.plot(
        x,
        [logc - v / k for v in x],
        "--",
        color="#c55911",
        lw=1.4,
        label=rf"Fixed $c_{k}t^{{-1/{k}}}$",
    )
    ax.set_xlabel(r"$\log_{10}t$")
    ax.set_ylabel(r"$\log_{10}$ normalized gap")
    ax.set_title(f'Order {k}: {d["actions"]} installed actions')
    ax.grid(alpha=0.2)
    ax.legend(fontsize=7.5)
    ax = axs[1, col]
    xx = [float(F(int(z["q"]), int(d["Q"]))) for z in p]
    err = [float(Decimal(z["ratio_to_asymptote"]) - 1) for z in p]
    ax.loglog(xx, err, "o-", ms=4, color="#1261a0")
    ax.set_xlabel(r"Phase ratio $q/Q$")
    ax.set_ylabel(r"$\mathrm{Gap}/(c_kt^{-1/k})-1$")
    ax.grid(alpha=0.2, which="both")
fig.suptitle("Finite hierarchical replay certifies every skipped decision", fontsize=13)
fig.tight_layout()
fig.savefig(H / "hierarchical_orders_4_5_6.png", dpi=180)
fig.savefig(H / "hierarchical_orders_4_5_6.pdf")
plt.close(fig)
