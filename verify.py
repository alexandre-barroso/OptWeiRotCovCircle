from fractions import Fraction as Q
from pathlib import Path
import json
import platform


def torus(x):
    y = x % 1
    return min(y, 1 - y)


def orbit_cones(alpha, r):
    limit = int(Q(1, 2) / r)
    return [((i * alpha) % 1, abs(i) * r) for i in range(-limit, limit + 1)]


def exact_maximum(alpha, r):
    cones = orbit_cones(alpha, r)
    nodes = sorted({Q(0), Q(1)} | {c for c, w in cones} | {(c + Q(1, 2)) % 1 for c, w in cones})
    best = Q(0)
    witness = Q(0)
    for left, right in zip(nodes, nodes[1:]):
        midpoint = (left + right) / 2
        plus = []
        minus = []
        for c, w in cones:
            d = (midpoint - c + Q(1, 2)) % 1 - Q(1, 2)
            v = abs(d) + w
            if d >= 0:
                plus.append(v - midpoint)
            else:
                minus.append(v + midpoint)
        candidates = [left, right]
        if plus and minus:
            crossing = (min(minus) - min(plus)) / 2
            if left <= crossing <= right:
                candidates.append(crossing)
        for x in candidates:
            v = min(w + torus(x - c) for c, w in cones)
            if v > best:
                best = v
                witness = x
    return best, witness


def formula(n, r):
    return (1 + 2 * n * (n + 1) * r) / (2 * (2 * n + 1))


def tiling(n, r):
    alpha = (2 - r) / (2 * n + 1)
    radius = formula(n, r)
    assert n * r <= radius <= (n + 1) * r
    total = sum(2 * max(Q(0), radius - abs(i) * r) for i in range(-n - 1, n + 2))
    assert total == 1
    centers = sorted(((i * alpha) % 1, i) for i in range(-n, n + 1))
    expected = [0]
    for j in range(1, n + 1):
        expected += [-n + j - 1, j]
    assert [i for c, i in centers] == expected
    for (c, i), (d, j) in zip(centers, centers[1:] + [(Q(1), 0)]):
        assert d - c == 2 * radius - (abs(i) + abs(j)) * r
    return alpha, radius

import os
os.environ.setdefault("MPLCONFIGDIR", str(Path(__file__).resolve().parent / ".mplconfig"))
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
BASE = Path(__file__).resolve().parent
plt.rcParams.update({"font.size": 9, "axes.labelsize": 9, "legend.fontsize": 8, "pdf.fonttype": 42, "ps.fonttype": 42, "lines.linewidth": 1.1})


def external_checks(out):
    import os
    import re
    import subprocess
    env = os.environ.copy()
    leanroot = env.get("LEAN_SYSROOT")
    prefix = [str(Path(leanroot) / "bin/lean")] if leanroot else ["lean"]
    command = prefix + ["-o", str(out / "Proofs.olean"), "Proofs.lean"]
    completed = subprocess.run(command, cwd=BASE, env=env, text=True, capture_output=True)
    log = completed.stdout + completed.stderr
    (out / "lean.log").write_text(log)
    assert completed.returncode == 0 and not re.search(r"sorryAx|PANIC|error:|unknown tactic", log), log
    audits = re.findall(r"depends on axioms: \[([^]]*)\]", log)
    assert audits
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    assert all(set(a.replace(" ", "").split(",")) <= allowed for a in audits)
    env["LEAN_PATH"] = str(out) + os.pathsep + env.get("LEAN_PATH", "")
    prefix = [str(Path(leanroot) / "bin/leanchecker")] if leanroot else ["leanchecker"]
    replay = subprocess.run(prefix + ["--fresh", "--verbose", "Proofs"], cwd=BASE, env=env, text=True, capture_output=True)
    (out / "lean_replay.log").write_text(replay.stdout + replay.stderr)
    assert replay.returncode == 0 and "PANIC" not in replay.stdout + replay.stderr
    wolfram = subprocess.run(["wolframscript", "-file", "verify.wls"], cwd=BASE, text=True, capture_output=True)
    (out / "wolfram.log").write_text(wolfram.stdout + wolfram.stderr)
    assert wolfram.returncode == 0 and "PASS" in wolfram.stdout, wolfram.stdout + wolfram.stderr
    return {"lean_exit": completed.returncode, "kernel_replay_exit": replay.returncode, "wolfram_exit": wolfram.returncode, "axiom_sets": audits}


def save_figure(fig, stem, out):
    folder = out / "figures"
    folder.mkdir(exist_ok=True)
    for ext in ["pdf", "png", "jpg", "eps"]:
        fig.savefig(folder / (stem + "." + ext), dpi=1500 if ext in ["png", "jpg"] else 600, bbox_inches="tight", facecolor="white")
    plt.close(fig)


def arguments():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--output", type=Path, default=BASE / "results")
    args = parser.parse_args()
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    return args


def main():
    args = arguments()
    cases = []
    exact_cases = 0
    for n in range(1, 51):
        low = Q(1, 2 * (n + 1) ** 2)
        high = Q(1, 2 * n ** 2)
        for r in [low, (3 * low + high) / 4, (low + high) / 2, (low + 3 * high) / 4, high]:
            alpha, value = tiling(n, r)
            if n <= 7:
                direct, witness = exact_maximum(alpha, r)
                assert direct == value
                mirror, unused = exact_maximum(1 - alpha, r)
                assert mirror == value
                exact_cases += 2
            cases.append({'n': n, 'r': str(r), 'alpha': str(alpha), 'radius': str(value)})
    comparisons = 0
    for r, n in [(Q(1, 4), 1), (Q(1, 8), 1), (Q(1, 12), 2), (Q(1, 18), 2), (Q(1, 25), 3)]:
        lower = formula(n, r)
        for k in range(65):
            alpha = Q(k, 64)
            value, witness = exact_maximum(alpha, r)
            assert value >= lower
            comparisons += 1
    special, witness = exact_maximum(Q(5, 12), Q(1, 4))
    assert special == Q(1, 3)
    assert exact_maximum(Q(1, 3), Q(1, 4))[0] == Q(5, 12)
    assert exact_maximum(Q(0), Q(1, 4))[0] == Q(1, 2)
    for r in [Q(1, 2), Q(3, 5), Q(1), Q(2)]:
        for alpha in [Q(0), Q(1, 7), Q(1, 2), Q(11, 12)]:
            assert exact_maximum(alpha, r)[0] == Q(1, 2)
    report = {'status': 'PASS', 'python': platform.python_version(), 'arithmetic': 'fractions.Fraction', 'tiling_cases': len(cases), 'independent_envelope_equalities': exact_cases, 'competitor_comparisons': comparisons, 'epsilon_quarter_example': {'alpha': '5/12', 'radius': str(special), 'witness': str(witness)}, 'limitations': 'Finite checks of exact rational instances; no substitute for the universal proof or novelty assessment.', 'cases': cases}
    plots(args.output)
    if args.all:
        report['external_checks'] = external_checks(args.output)
    out = args.output / 'verification_results.json'
    out.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'cases'}, indent=2))


def plots(out):
    fig, axes = plt.subplots(2, 1, figsize=(4.685, 4.7))
    noise = np.geomspace(0.003, 0.5, 500)
    values = []
    for r in noise:
        n = max(1, int(1 / np.sqrt(2*r)))
        values.append(float(formula(n, r)))
    axes[0].loglog(noise, values, color="black", label="Exact optimum")
    axes[0].loglog(noise, np.sqrt(noise/2), color="0.5", linestyle="--", label=r"$\sqrt{r/2}$")
    axes[0].set(xlabel=r"Noise ratio $r=\epsilon/L$", ylabel=r"Normalized radius $R_*(r)$")
    axes[0].legend(frameon=False)
    axes[0].set_title("(a)", loc="left", fontsize=9)
    x = np.linspace(0, 1, 1001)
    for a, style, label in [(5/12, "-", r"$\alpha=5/12$"), (1/3, "--", r"$\alpha=1/3$")]:
        y = np.min([abs(i)/4 + np.minimum((x-i*a)%1, 1-(x-i*a)%1) for i in range(-2,3)],axis=0)
        axes[1].plot(x,y,linestyle=style,color="black",label=label)
    axes[1].set(xlabel=r"$x$ on the unit circle",ylabel=r"$d_{\alpha,1/4}(x)$",xlim=(0,1),ylim=(0,0.46))
    axes[1].legend(frameon=False)
    axes[1].set_title("(b)", loc="left", fontsize=9)
    fig.tight_layout()
    save_figure(fig,"Fig1",out)


if __name__ == '__main__':
    main()
