# Public-package portability changes

The files listed under `unchanged_copies` in `source_manifest.json` are byte-identical to their research archive. This includes source proofs, separate internal reviews, both diagnostic trajectories, and historical certificates. Historical proof headers can say “awaiting review”; the corresponding later source-bound review is included separately. The README gives current status.

The archive paths in that manifest are relative to the original attention project. Not every historical dependency, paper download or earlier abandoned experiment is part of this focused release. Each included proof states its actual architecture and restrictions. The original paper is linked rather than copied.

Three original scripts depended on a local portfolio layout and dependency directory. Their original hashes are recorded, but the scripts are not published as runnable entrypoints:

| Original script | Public replacement | Change |
|---|---|---|
| `check_algebra_and_retained_states.py` | `verify.py` | Combined exact/retained-data checks, resolved relative to this package; no local dependency injection |
| `check_three_halves_interface.py` | `verify.py --native` | Same mathematical interface comparison, extended to both p=2 and p=3/2; pinned explicit optimizer fetch; generic-p finite geometry checks added |
| `run_fixed_diagnostic.py` | `run_diagnostic.py --output-dir NEW_DIR` | Both fixed trajectories preserved; new output directory and provenance fields; ordinary installed dependencies and explicit verified optimizer cache |

These are new script bytes, with new hashes in `release_manifest.json`; they are not passed off as the historical certificate-producing scripts. The historical certificates describe their original runs. `release_verification.json` describes the checks actually executed on this portable package. No training trajectory was rerun during release preparation.

The optional reproduction retains the original loop and numerical operations, including the two independent cases, paired-sign examples, 50,000 steps, eta=.1, p=2, full-matrix autograd, all scheduled states and both outcomes. Its protocol has a fresh timestamp and producer hash and links the original protocol. Consequently reproduction output hashes are not expected to equal the historical hashes.

`fetch_optimizer.py` is new and fetches only the official optimizer at the recorded commit, checking SHA256 before saving or loading it. `external_cache/`, local virtual environments, bytecode and new runs are git-ignored and excluded from the release manifest.
