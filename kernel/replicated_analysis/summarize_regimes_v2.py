"""Protocol-role revision v2; all statistical definitions unchanged.

Postprocess only the complete, audited 15-shard aggregate.

All outcome values are read from aggregate.json. Per-shard audit files are
read only for pass/completion/source metadata. No raw or partial cell files,
trial files, solver implementations, or cloud APIs are accessed.
"""
from argparse import ArgumentParser
from datetime import datetime, timezone
import csv
import hashlib
import itertools
import json
import math
from pathlib import Path
import statistics
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "attention" / "deps"))
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import SymLogNorm, TwoSlopeNorm

T4 = 2.7764451051977987
PAIRS = [
    ("official_askotchv2", "inducing_pcg_falkon"),
    ("corrected_askotchv2", "inducing_pcg_falkon"),
    ("official_askotchv2", "corrected_askotchv2"),
]
LABELS = {"corrected_askotchv2": "Corrected ASkotchV2",
          "official_askotchv2": "Released ASkotchV2",
          "inducing_pcg_falkon": "Inducing PCG/Falkon"}
KERNEL_LABELS = {"matern_0.5": "Matérn ν=0.5", "matern_2.5": "Matérn ν=2.5", "rbf": "RBF"}
STEMS = ["official_vs_inducing", "corrected_vs_inducing", "official_vs_corrected"]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def close(a, b):
    return math.isclose(float(a), float(b), rel_tol=1e-10, abs_tol=1e-12)


def paired_stats(values):
    require(len(values) == 5 and all(math.isfinite(x) for x in values), "Expected five finite seed effects")
    mean = statistics.mean(values)
    sd = statistics.stdev(values)
    se = sd / math.sqrt(5)
    return {"mean": mean, "sample_sd": sd, "standard_error": se,
            "descriptive_t4_95_interval": [mean-T4*se, mean+T4*se]}


def load_complete_inputs(directory, config_path):
    # Check the completion marker before opening any outcome aggregate.
    status_path = directory / "aggregate_status.json"
    status = json.loads(status_path.read_text())
    require(status.get("status") == "complete_descriptive_grid" and status.get("models") == 270,
            "Aggregate is not marked complete; no outcomes were opened")
    cfg = json.loads(config_path.read_text())
    require(cfg["n_train"] == [512, 2048, 8192], "Unexpected frozen sample-size grid")
    require(cfg["kernels"] == ["matern_0.5", "matern_2.5", "rbf"], "Unexpected kernel grid")
    require(cfg["noise_sd"] == [0.05, 0.3] and cfg["seeds"] == [11, 23, 47, 83, 131], "Unexpected noise/seed grid")
    require(set(cfg["methods"]) == {m for pair in PAIRS for m in pair}, "Unexpected methods")
    freeze_path = config_path.parent / "freeze.json"
    freeze = json.loads(freeze_path.read_text())
    require(digest(config_path) == freeze["sha256"]["regime_replicates/config.json"], "Frozen config changed")
    audits = []
    for n, seed in itertools.product(cfg["n_train"], cfg["seeds"]):
        audit_path = directory / f"n{n}_seed{seed}" / "audit.json"
        audit = json.loads(audit_path.read_text())
        require(audit.get("status") == "passed" and not audit.get("issues"), f"Shard audit failed: n={n}, seed={seed}")
        require(audit.get("expected_workers") == audit.get("observed_workers") == 18, "Shard worker coverage mismatch")
        require(audit.get("source_commit") == cfg["source_commit"], "Shard source pin mismatch")
        audits.append({"n": n, "seed": seed, "audit_sha256": digest(audit_path),
                       "summary_sha256": audit["summary_sha256"], "config_sha256": audit["config_sha256"]})
    aggregate_path = directory / "aggregate.json"
    aggregate = json.loads(aggregate_path.read_text())
    require(aggregate.get("status") == "complete_descriptive_grid", "Aggregate payload is not complete")
    require((aggregate.get("cells"), aggregate.get("models"), aggregate.get("seed_count")) == (90, 270, 5), "Aggregate counts differ")
    provenance = {"aggregate_sha256": digest(aggregate_path), "aggregate_status_sha256": digest(status_path),
                  "config_sha256": digest(config_path), "run_freeze_sha256": digest(freeze_path),
                  "aggregate_source_sha256": digest(directory / "aggregate.py"),
                  "shard_audit_source_sha256": digest(directory / "audit_shard.py"),
                  "analysis_source_sha256": digest(Path(__file__)), "passed_shard_audits": audits}
    return cfg, aggregate, provenance


def independent_summary(cfg, aggregate):
    regimes = list(itertools.product(cfg["n_train"], cfg["kernels"], cfg["noise_sd"]))
    expected = {(n,k,float(noise),left,right) for n,k,noise in regimes for left,right in PAIRS}
    comparisons = aggregate["paired_comparisons"]
    require(len(comparisons) == 54, "All 18 regimes and all three comparisons are required")
    by_key, model_values = {}, {}
    for comparison in comparisons:
        key = (comparison["n"], comparison["kernel"], float(comparison["noise_sd"]), comparison["left"], comparison["right"])
        require(key in expected and key not in by_key, "Missing, unexpected, or duplicated comparison")
        raw = comparison["raw_seeds"]
        require(len(raw) == 5 and {r["seed"] for r in raw} == set(cfg["seeds"]), "Missing or duplicate paired seeds")
        raw_by_seed = {r["seed"]: r for r in raw}
        differences, relative, seed_rows = [], [], []
        for seed in cfg["seeds"]:
            row = raw_by_seed[seed]
            left, right = float(row["left_test_mse"]), float(row["right_test_mse"])
            require(math.isfinite(left) and math.isfinite(right) and left >= 0 and right > 0,
                    "Nonfinite/negative MSE or undefined relative effect; do not omit the cell")
            difference = left-right
            relative_percent = 100*difference/right
            require(close(difference,row["difference"]), "Stored seed difference disagrees with its MSEs")
            differences.append(difference)
            relative.append(relative_percent)
            for side in ("left", "right"):
                method = comparison[side]
                model_key = key[:3] + (seed, method)
                value = (float(row[f"{side}_test_mse"]), float(row[f"{side}_lambda"]), str(row[f"{side}_capacity"]))
                if model_key in model_values:
                    prior = model_values[model_key]
                    require(close(prior[0],value[0]) and close(prior[1],value[1]) and prior[2] == value[2],
                            "A model's MSE/selection differs between comparison records")
                model_values[model_key] = value
            seed_rows.append({"seed": seed, "left_test_mse": left, "right_test_mse": right,
                              "difference": difference, "relative_percent": relative_percent})
        absolute, percent = paired_stats(differences), paired_stats(relative)
        require(close(absolute["mean"], comparison["mean_paired_difference"]), "Aggregate mean mismatch")
        require(close(absolute["standard_error"], comparison["paired_seed_standard_error"]), "Aggregate standard error mismatch")
        require(all(close(a,b) for a,b in zip(absolute["descriptive_t4_95_interval"], comparison["student_t4_95_interval"])), "Aggregate interval mismatch")
        wins = sum(x < 0 for x in differences)
        require(wins == comparison["left_wins_out_of_5"], "Aggregate paired sign count mismatch")
        by_key[key] = {"n": key[0], "kernel": key[1], "noise_sd": key[2], "left": key[3], "right": key[4],
                       "left_mean_test_mse": statistics.mean(r["left_test_mse"] for r in seed_rows),
                       "right_mean_test_mse": statistics.mean(r["right_test_mse"] for r in seed_rows),
                       "paired_difference": absolute, "paired_relative_percent": percent,
                       "left_lower_mse_seed_count": wins, "seed_rows": seed_rows}
    require(set(by_key) == expected and len(model_values) == 270, "Incomplete regime/model coverage")
    # The order is fixed from the protocol, never sorted by observed effects.
    return [by_key[(n,k,float(noise),left,right)] for left,right in PAIRS for n,k,noise in regimes]


def figure_style():
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10,
                         "axes.spines.top": False, "axes.spines.right": False,
                         "pdf.fonttype": 42, "ps.fonttype": 42})


def render_grid(cfg, rows, pair_index, output):
    left, right = PAIRS[pair_index]
    selected = [r for r in rows if (r["left"], r["right"]) == (left,right)]
    lookup = {(r["n"],r["kernel"],r["noise_sd"]):r for r in selected}
    fig, axes = plt.subplots(2,2,figsize=(15.8,9.3),layout="constrained")
    metrics = [("paired_difference", "Mean paired test-MSE difference"),
               ("paired_relative_percent", "Mean seedwise relative effect (%)")]
    for col,(field,title) in enumerate(metrics):
        limit = max(abs(r[field]["mean"]) for r in selected) or 1.
        norm = TwoSlopeNorm(vmin=-limit,vcenter=0,vmax=limit) if col == 0 else SymLogNorm(linthresh=1.,vmin=-limit,vmax=limit,base=10)
        for noise_index,noise in enumerate(cfg["noise_sd"]):
            ax = axes[noise_index,col]
            matrix = np.array([[lookup[(n,k,noise)][field]["mean"] for n in cfg["n_train"]] for k in cfg["kernels"]])
            image = ax.imshow(matrix,cmap="RdBu_r",norm=norm,aspect="auto")
            for j,kernel in enumerate(cfg["kernels"]):
                for i,n in enumerate(cfg["n_train"]):
                    stat = lookup[(n,kernel,noise)][field]
                    mean = stat["mean"]; low,high = stat["descriptive_t4_95_interval"]
                    line1 = f"{mean:+.3e}" if col == 0 else f"{mean:+.2f}%"
                    line2 = f"[{low:+.2e}, {high:+.2e}]" if col == 0 else f"[{low:+.2f}, {high:+.2f}]"
                    rgba = plt.get_cmap("RdBu_r")(norm(mean))
                    luminance = .2126*rgba[0]+.7152*rgba[1]+.0722*rgba[2]
                    ax.text(i,j,line1+"\n"+line2,ha="center",va="center",fontsize=9,color="white" if luminance<.48 else "#111111")
            ax.set_xticks(range(3),[f"n={n:,}" for n in cfg["n_train"]])
            ax.set_yticks(range(3),[KERNEL_LABELS[k] for k in cfg["kernels"]])
            ax.set_title(f"{title}\nNoise SD={noise:g}",fontsize=11,pad=12)
            ax.set_xticks(np.arange(-.5,3,1),minor=True)
            ax.set_yticks(np.arange(-.5,3,1),minor=True)
            ax.grid(which="minor",color="white",linewidth=2)
            ax.tick_params(which="minor",bottom=False,left=False)
        bar = fig.colorbar(image,ax=axes[:,col],shrink=.7,pad=.02)
        bar.set_label("Paired mean ΔMSE" if col == 0 else "Paired mean relative % (symlog color, linear within ±1%)")
    role = "Primary comparison" if pair_index == 0 else "Implementation diagnostic"
    fig.suptitle(f"{role}: {LABELS[left]} minus {LABELS[right]}\n"
                 "All 18 regimes · five paired seeds · brackets: descriptive 95% t₄ intervals\n"
                 "Negative = smaller left-method MSE; positive = smaller right-method MSE",
                 fontsize=13)
    fig.canvas.draw()
    stem = output / f"regime_grid_{STEMS[pair_index]}"
    fig.savefig(stem.with_suffix(".png"),dpi=190,bbox_inches="tight")
    fig.savefig(stem.with_suffix(".pdf"),bbox_inches="tight")
    plt.close(fig)


def render_primary_seeds(cfg, rows, output):
    selected = [r for r in rows if (r["left"],r["right"]) == PAIRS[0]]
    lookup = {(r["n"],r["kernel"],r["noise_sd"]):r for r in selected}
    fig,axes = plt.subplots(3,2,figsize=(12.5,10),sharex=True,sharey=True,layout="constrained")
    all_values = [x for r in selected for x in r["paired_relative_percent"]["descriptive_t4_95_interval"]]
    all_values += [s["relative_percent"] for r in selected for s in r["seed_rows"]]
    limit = max(map(abs,all_values)) or 1.
    for ni,n in enumerate(cfg["n_train"]):
        for sj,noise in enumerate(cfg["noise_sd"]):
            ax = axes[ni,sj]
            for ki,kernel in enumerate(cfg["kernels"]):
                row = lookup[(n,kernel,noise)]
                values = [s["relative_percent"] for s in row["seed_rows"]]
                ax.scatter(values,ki+np.linspace(-.12,.12,5),s=20,color="#767676",alpha=.8,zorder=2)
                stat = row["paired_relative_percent"]; mean=stat["mean"]; lo,hi=stat["descriptive_t4_95_interval"]
                ax.errorbar([mean],[ki],xerr=[[mean-lo],[hi-mean]],fmt="D",color="#123A59",capsize=4,markersize=5,zorder=3)
            ax.axvline(0,color="#333333",linestyle="--",linewidth=.8)
            ax.set_xscale("symlog",linthresh=1,base=10)
            ax.set_xlim(-1.1*limit,1.1*limit)
            ax.set_yticks(range(3),[KERNEL_LABELS[k] for k in cfg["kernels"]])
            ax.set_ylim(2.5,-.5)
            ax.grid(axis="x",alpha=.18)
            ax.set_title(f"n={n:,} · noise SD={noise:g}")
    fig.supxlabel("100 × (released MSE − inducing MSE) / inducing MSE; symlog axis, linear within ±1%")
    fig.suptitle("Primary comparison: every paired seed, all 18 regimes\n"
                 "Gray points: five seeds in fixed order; diamond/bar: paired mean and descriptive 95% t₄ interval",
                 fontsize=12)
    fig.canvas.draw()
    stem = output / "paired_seed_effects_official_vs_inducing"
    fig.savefig(stem.with_suffix(".png"),dpi=190,bbox_inches="tight")
    fig.savefig(stem.with_suffix(".pdf"),bbox_inches="tight")
    plt.close(fig)


def save_tables(rows, output):
    table, seeds = [], []
    for row in rows:
        base = {k:row[k] for k in ("n","kernel","noise_sd","left","right")}
        a,r = row["paired_difference"],row["paired_relative_percent"]
        table.append(dict(base,left_mean_test_mse=row["left_mean_test_mse"],right_mean_test_mse=row["right_mean_test_mse"],
                          mean_difference=a["mean"],difference_se=a["standard_error"],difference_t4_low=a["descriptive_t4_95_interval"][0],difference_t4_high=a["descriptive_t4_95_interval"][1],
                          mean_relative_percent=r["mean"],relative_percent_se=r["standard_error"],relative_percent_t4_low=r["descriptive_t4_95_interval"][0],relative_percent_t4_high=r["descriptive_t4_95_interval"][1],
                          left_lower_mse_seed_count=row["left_lower_mse_seed_count"]))
        seeds.extend(dict(base,**seed) for seed in row["seed_rows"])
    for name,records in (("regime_summary.csv",table),("paired_seed_effects.csv",seeds)):
        with (output/name).open("w",newline="") as stream:
            writer=csv.DictWriter(stream,fieldnames=list(records[0]));writer.writeheader();writer.writerows(records)


def write_report(cfg, aggregate, summary, output):
    rows=summary["regimes"]
    primary=[r for r in rows if (r["left"],r["right"])==PAIRS[0]]
    lines=["# Complete replicated kernel regime grid — protocol-primary revision", "",
           "**Version 2 correction:** the frozen [PROTOCOL](../../regime_replicates/PROTOCOL.md) designates released ASkotchV2 versus inducing as primary and corrected ASkotchV2 as diagnostic. Version 1 followed an incorrect preparation instruction that reversed those roles. This version restores the protocol roles; no MSE, seed, interval, selected model, hyperparameter or comparison estimate changes. The old renderer, freeze and figures are preserved. See the [correction record](../protocol_role_correction.json).", "",
           "Implementation names: the inducing comparator is the same pinned fast_krr repository’s InducingKRR and PCG with its Falkon preconditioner, not a claim to execute the separate official Falkon package. The released and corrected full solvers use the same frozen acceleration safeguard; the corrected arm changes the stale block-regularizer evaluation. Figure labels identify these frozen code paths.", "",
           "All 15 shard audits passed before this analysis read the aggregate: 18 regimes × five seeds = 90 seed-specific cells, with three selected models per cell (270 models). All regimes and seeds are retained in protocol order.", "",
           "The protocol-primary contrast is released ASkotchV2 minus inducing PCG/Falkon on selected-model test MSE. For each seed, d=L−R and r=100(L−R)/R. The displayed relative effect is the mean of the five seedwise percentages, not a ratio of mean MSEs. Negative values mean lower MSE for the left method.", "",
           "Each interval is mean ± 2.7764451051977987 × sample-SD/√5, calculated separately for d and r. These are descriptive paired-t₄ intervals with only five replicates; their nominal interpretation needs appropriate independence and distributional assumptions. There is no multiplicity correction across the 18 regimes, no interpolated crossover boundary, and no universal superiority claim. Comparisons within a seed use paired test streams; different regimes are not pooled into a winner score.", "",
           f"Each method was offered the same frozen search: {len(cfg['lambda_unscaled'])*len(cfg['capacity'])} candidates with {cfg['trial_seconds']:g} synchronized seconds per candidate, including fresh measured construction and selection work. Symmetric discarded warmup was recorded separately. This is warmed implementation performance, not cold end-to-end timing. A method may stop early and leave available time unused. Selected models were frozen before test creation according to the shard audits; those audits qualify the timestamp/source-order evidence.", "",
           "## Primary comparison: every regime", "",
           "| n | Kernel | Noise SD | Mean ΔMSE [t₄ interval] | Mean relative % [t₄ interval] | Left smaller / 5 |",
           "|---:|---|---:|---:|---:|---:|"]
    for row in primary:
        a,r=row["paired_difference"],row["paired_relative_percent"]
        lo,hi=a["descriptive_t4_95_interval"];rl,rh=r["descriptive_t4_95_interval"]
        lines.append(f"| {row['n']} | {KERNEL_LABELS[row['kernel']]} | {row['noise_sd']:g} | {a['mean']:+.4e} [{lo:+.3e}, {hi:+.3e}] | {r['mean']:+.3f}% [{rl:+.3f}, {rh:+.3f}] | {row['left_lower_mse_seed_count']} |")
    lines += ["", "[Primary regime grid](regime_grid_official_vs_inducing.pdf) · [All paired seeds](paired_seed_effects_official_vs_inducing.pdf)", "",
              "## Separate implementation diagnostics", "",
              "The [corrected-minus-inducing grid](regime_grid_corrected_vs_inducing.pdf) and [released-minus-corrected grid](regime_grid_official_vs_corrected.pdf) retain the same 18 regimes and five paired seeds. They describe the frozen implementations. Their differences cannot be attributed solely to the block-gradient correction because timed iteration counts and selected settings may also differ. They do not establish a theorem about either algorithm, and the correction's theoretical projection bounds are not certified by this benchmark. Color scales are shared within each figure/metric, not across different comparison figures.", "",
              f"The aggregate records {len(aggregate['numerical_failure_outcomes'])} candidate-exception or missing-eligible-checkpoint records. This narrow field does not count nonfinite iteration stops: the complete raw-source audit found eight inducing trials that stopped on a nonfinite iterate; every one retained an earlier eligible checkpoint, and none of the eight candidates was selected. All eight were n=8192, RBF, large capacity, at lambda 1e-8 or 1e-6. They remain in the raw results. Across all 270 selected models, {aggregate['lambda_endpoint_selections']} selected a lambda endpoint, which remains unresolved tuning.", "",
              "The raw timing audit records 1,020 inducing residual-tolerance stops, 52 budget stops and eight nonfinite stops. Mean measured candidate time was 0.306008 seconds for inducing, 4.007410 seconds for released ASkotchV2 and 4.007306 seconds for corrected ASkotchV2. Thus the experiment equalizes available four-second caps and candidate counts, not consumed wall time. Inducing left about 3.694087 seconds per candidate unused on average. Warmup is separate. Residual-tolerance stopping uses the recursively maintained PCG residual, not an independent direct residual or optimality certificate. [Full stop/timing audit](../complete_source_and_timing_audit.json).", "",
              "## Reproducibility", "",
              "[Complete aggregate](../aggregate.json) · [Independent summary](regime_summary.json) · [All 54 comparison rows](regime_summary.csv) · [All 270 paired seed effects](paired_seed_effects.csv)", "",
              f"Aggregate SHA-256: `{summary['provenance']['aggregate_sha256']}`.", "",
              f"Analysis source SHA-256: `{summary['provenance']['analysis_source_sha256']}`.", "",
              "The independent summary recomputes differences and t intervals from aggregate.raw_seeds and checks them against the aggregator. It also checks cross-comparison MSE/selection consistency, all 270 model identities, and all 15 passed shard-audit metadata records. No partial cell/trial outcome file is used.", ""]
    (output/"REGIME_REPORT.md").write_text("\n".join(lines))


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--directory",type=Path,default=HERE)
    parser.add_argument("--config",type=Path,default=HERE.parent/"regime_replicates"/"config.json")
    parser.add_argument("--output",type=Path,default=HERE/"report_v2")
    args=parser.parse_args()
    cfg,aggregate,provenance=load_complete_inputs(args.directory,args.config)
    rows=independent_summary(cfg,aggregate)
    summary={"status":"complete_independently_recomputed_descriptive_grid", "created_utc":datetime.now(timezone.utc).isoformat(),
             "regime_count":18,"paired_seeds_per_regime":5,"model_count":270,"provenance":provenance,
             "relative_effect_definition":"mean_s[100*(left_test_mse_s-right_test_mse_s)/right_test_mse_s]",
             "interval_definition":"descriptive mean ± t_(4,.975)*sample_sd/sqrt(5), separately for absolute and relative paired effects",
             "critical_t4":T4,"regimes":rows,
             "lambda_endpoint_selections":aggregate["lambda_endpoint_selections"],
             "capacity_selections":aggregate["capacity_selections"],
             "numerical_failure_outcomes":aggregate["numerical_failure_outcomes"],
             "scope":"All fixed regimes; no multiplicity correction, continuous regime-boundary inference, or universal winner claim."}
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/"regime_summary.json").write_text(json.dumps(summary,indent=2)+"\n")
    save_tables(rows,args.output)
    figure_style()
    for pair_index in range(3):
        render_grid(cfg,rows,pair_index,args.output)
    render_primary_seeds(cfg,rows,args.output)
    write_report(cfg,aggregate,summary,args.output)
    print(json.dumps({"status":summary["status"],"regimes":18,"models":270,"output":str(args.output)},indent=2))


if __name__=="__main__":
    main()

