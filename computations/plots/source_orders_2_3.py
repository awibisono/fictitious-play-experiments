"""Source plot for the order-two and order-three numerical arrays.

Used by make_print_figures.py; output is captured before serialization.
"""

if not __debug__:
    raise RuntimeError("Exact verification requires Python without -O or -OO.")

from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal, localcontext
import json, sys

sys.set_int_max_str_digits(0)
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

plt.rcParams.update(
    {
        "font.size": 10,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "pdf.fonttype": 42,
    }
)
DATA_ROOT = Path(__file__).resolve().parent.parent
ROOT = Path(__file__).resolve().parent / "generated"
summary = json.loads((DATA_ROOT / "summary.json").read_text())


def dec(x):
    x = F(x)
    return Decimal(x.numerator) / Decimal(x.denominator)


def lg(x):
    return dec(x).log10()


def load(k):
    return json.loads(
        (DATA_ROOT / f"order{k}_construction.json").read_text()
    ), json.loads((DATA_ROOT / f"order{k}_event_result.json").read_text())


with localcontext() as ctx:
    ctx.prec = 85
    # Exact trajectory samples for orders two and three.
    fig, axs = plt.subplots(
        2, 2, figsize=(11, 7.4), gridspec_kw={"height_ratios": [2, 1]}
    )
    for col, k in enumerate([2, 3]):
        d, r = load(k)
        ss = r["samples"]
        st = summary[k - 2]
        x = [s["log10_t"] for s in ss]
        y = [s["log10_normalized_gap"] for s in ss]
        ax = axs[0, col]
        ax.plot(
            x, y, color="#1261a0", lw=1.8, label="Exact certified trajectory samples"
        )
        xmin = max(0, x[-1] - 7)
        xx = [xmin, x[-1]]
        lc = float(st["log10_normalized_constant"])
        ax.plot(
            xx,
            [lc - z / k for z in xx],
            "--",
            color="#c55911",
            label=r"$c_k\,t^{-1/k}$ (fixed formula)",
        )
        ax.set_xlabel(r"$\log_{10} t$")
        ax.set_ylabel(r"$\log_{10}\mathrm{Gap}_{A/\|A\|_{\max}}$")
        ax.set_title(
            f'Order {k}: {st["actions"]} actions, {int(st["completed_outer_phases"]):,} complete phases'
        )
        ax.legend(fontsize=8)
        ax.grid(alpha=0.2)
        ratios = []
        for s in ss:
            ratios.append(
                float(
                    lg(F(s["gap"]))
                    + Decimal(s["t"]).log10() / k
                    - lg(F(d["rate_constant_power_k"])) / k
                )
            )
        ax = axs[1, col]
        ax.plot(x, ratios, color="#1261a0", lw=1.4)
        ax.axhline(0, color="#c55911", ls="--")
        ax.set_xlim(max(0, x[-1] - 4), x[-1])
        tail = [v for z, v in zip(x, ratios) if z >= x[-1] - 4]
        ax.set_ylim(min(-0.003, min(tail) * 1.1), max(0.004, max(tail) * 1.1))
        ax.set_xlabel(r"$\log_{10} t$ (tail)")
        ax.set_ylabel(r"$\log_{10}[\mathrm{Gap}/(c_kt^{-1/k})]$")
        ax.grid(alpha=0.2)
    fig.suptitle(
        "RPS-based games: exact simultaneous fictitious play from the setup move",
        fontsize=13,
    )
    fig.tight_layout()
    fig.savefig(ROOT / "exact_observed_orders_2_3.png", dpi=180)
    fig.savefig(ROOT / "exact_observed_orders_2_3.pdf")
    plt.close(fig)
