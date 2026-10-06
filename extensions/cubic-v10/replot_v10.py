"""Replot verified exact saved states; no new trajectory points are invented."""

from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal, localcontext
import argparse, json, sys

sys.set_int_max_str_digits(0)
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator, LogLocator

p = argparse.ArgumentParser()
p.add_argument("--data-root", type=Path, required=True)
p.add_argument("--output-dir", type=Path, required=True)
a = p.parse_args()
R = a.data_root
O = a.output_dir
O.mkdir(parents=True, exist_ok=True)
plt.rcParams.update(
    {
        "font.size": 9,
        "axes.titlesize": 10,
        "axes.labelsize": 9,
        "xtick.labelsize": 8,
        "ytick.labelsize": 8,
        "legend.fontsize": 8,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "pdf.fonttype": 42,
    }
)
blue = "#1261a0"
orange = "#c55911"
report = {}
with localcontext() as ctx:
    ctx.prec = 85
    dc = lambda f: Decimal(f.numerator) / Decimal(f.denominator)

    def vals(k, points, norm):
        cons = json.loads((R / f"order{k}_construction.json").read_text())
        cp = dc(F(cons["rate_constant_power_k"]))
        lc = cp.log10() / k - dc(norm).log10()
        x = []
        y = []
        rat = []
        for s in points:
            t = Decimal(s["t"])
            g = F(s["gap"])
            x.append(float(t.log10()))
            y.append(float(dc(g / norm).log10()))
            rat.append(float(dc(g).log10() + t.log10() / k - cp.log10() / k))
            assert F(s["normalized_gap"]) == g / norm
        return x, y, rat, float(lc)

    fig, axs = plt.subplots(2, 2, figsize=(6.5, 5.9))
    for row, k in enumerate([2, 3]):
        d = json.loads((R / f"order{k}_event_result.json").read_text())
        norm = F(int(d["normalization_max_scaled"]), int(d["integer_scale"]))
        x, y, rat, lc = vals(k, d["samples"], norm)
        xmax = 12 if k == 2 else max(x)
        ax = axs[row, 0]
        ax.plot(x, y, color=blue, lw=1.25, label="Exact replay")
        xx = [0 if k == 2 else 12, xmax]
        ax.plot(
            xx,
            [lc - v / k for v in xx],
            ls="--",
            color=orange,
            lw=1.2,
            label=rf"$\widetilde c_{k}t^{{-1/{k}}}$",
        )
        ax.set_xlim(0, xmax)
        visible = [yy for xx, yy in zip(x, y) if xx <= xmax]
        lo = min(visible + [lc - xmax / k])
        hi = max(visible)
        ax.set_ylim(lo - 0.25, hi + 0.25)
        ax.set_title(f"Order {k}: observed gap", loc="left")
        ax.set_xlabel(r"$\log_{10}t$")
        ax.set_ylabel(r"$\log_{10}$ payoff-scaled gap")
        ax.legend(loc="upper right", framealpha=0.95)
        ax.grid(alpha=0.2)
        ax.xaxis.set_major_locator(MaxNLocator(4))
        ax.yaxis.set_major_locator(MaxNLocator(5))
        ax = axs[row, 1]
        ax.plot(x, rat, color=blue, lw=1.25)
        lim = (0, 8) if k == 2 else (12, max(x))
        ax.set_xlim(*lim)
        visible = [v for z, v in zip(x, rat) if lim[0] <= z <= lim[1]]
        ax.set_ylim(-0.015, max(visible) * 1.05)
        ax.set_title("Approach to the predicted rate", loc="left")
        ax.set_xlabel(r"$\log_{10}t$ (onset window)")
        ax.set_ylabel(r"$\log_{10}[g/(c_k t^{-1/k})]$")
        ax.grid(alpha=0.2)
        ax.xaxis.set_major_locator(MaxNLocator(4))
        ax.yaxis.set_major_locator(MaxNLocator(5))
        ax.axhline(0, color=orange, ls="--", lw=1)
        report[str(k)] = {
            "source_samples": len(x),
            "gap_xlim": [0, xmax],
            "ratio_xlim": list(lim),
        }
    fig.subplots_adjust(
        left=0.115, right=0.985, bottom=0.085, top=0.945, wspace=0.5, hspace=0.51
    )
    fig.savefig(O / "exact_observed_orders_2_3_v10.pdf")
    fig.savefig(O / "exact_observed_orders_2_3_v10.png", dpi=180)
    plt.close(fig)
    fig, axs = plt.subplots(3, 2, figsize=(6.5, 7.2))
    for row, k in enumerate([4, 5, 6]):
        d = json.loads(
            (R / "hierarchical" / f"order{k}_recursive_replay.json").read_text()
        )
        p = (
            json.loads(
                (R / "hierarchical" / "order6_dense_certified_samples.json").read_text()
            )["samples"]
            if k == 6
            else d["samples"]
        )
        p = p[2:]
        norm = F(int(d["normalization_max_scaled"]), int(d["integer_scale"]))
        x, y, rat, lc = vals(k, p, norm)
        ax = axs[row, 0]
        ax.plot(x, y, "o-", color=blue, ms=2.8, lw=1.25, label="Certified phase starts")
        ax.plot(
            x,
            [lc - v / k for v in x],
            "--",
            color=orange,
            lw=1.2,
            label=rf"$\widetilde c_{k}t^{{-1/{k}}}$",
        )
        ax.set_title(f"Order {k}: phase-start gaps", loc="left")
        ax.set_xlabel(r"$\log_{10}t$")
        ax.set_ylabel(r"$\log_{10}$ payoff-scaled gap")
        ax.legend(loc="upper right", framealpha=0.95)
        ax.grid(alpha=0.2)
        ax.xaxis.set_major_locator(MaxNLocator(4))
        ax.yaxis.set_major_locator(MaxNLocator(4))
        ax = axs[row, 1]
        xx = [float(F(int(s["q"]), int(d["Q"]))) for s in p]
        err = [float(Decimal(s["ratio_to_asymptote"]) - 1) for s in p]
        ax.semilogy(x, err, "o-", color=blue, ms=2.8, lw=1.25)
        ax.set_title("Relative error at phase starts", loc="left")
        ax.set_xlabel(r"$\log_{10}t$")
        ax.set_ylabel(r"$g/(c_k t^{-1/k})-1$")
        ax.xaxis.set_major_locator(MaxNLocator(4))
        ax.set_xlim(axs[row, 0].get_xlim())
        ax.yaxis.set_major_locator(LogLocator(base=10, numticks=4))
        ax.grid(alpha=0.2)
        report[str(k)] = {
            "source_samples": len(x),
            "phase_ratios": xx,
            "log10_t": x,
            "gap_xlim": list(axs[row, 0].get_xlim()),
            "ratio_xlim": list(ax.get_xlim()),
        }
    fig.subplots_adjust(
        left=0.135, right=0.985, bottom=0.07, top=0.96, wspace=0.52, hspace=0.65
    )
    fig.savefig(O / "hierarchical_orders_4_5_6_v10.pdf")
    fig.savefig(O / "hierarchical_orders_4_5_6_v10.png", dpi=180)
    plt.close(fig)

(O / "plot_report.json").write_text(json.dumps(report, indent=2) + "\n")
