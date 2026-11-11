# herd7 tests of the RC11 reference model

These tests exercise the RC11 reference model, not the ERN fragment.

They fix the reference point that WC5.1 C53 calls the "complete external RC11 reference". They check what RC11 says about the patterns WC5.1 relies on: release/acquire message passing, the reference mutex, exclusive acquisition by an RMW, release sequences, load buffering and mixed atomic/non-atomic accesses. Exploratory work, never merged.

## Contents

- `litmus/`: one C litmus test per file, in the herd7 C dialect.
  - Group A, memory orders: `MP+rel+acq`, `MP+rlx+rlx`, `MP+sc+sc`, `LB+rlx`.
  - Group B, reference mutex: `LOCK+xchg-acq+rel`, `LOCK+xchg-acq+rlx`, `LOCK+xchg-rlx+rel`, `LOCK+sc+sc`, `LOCK+cas-acq+rel`, `LOCK3+xchg-acq+rel`.
  - Group C, mixed accesses: `MIX+store-rlx+read`, `AT+store+store`, `NA+write+write`.
  - Group D, exclusive acquisition: `XCHG+acq`, `XCHG+rlx`, `XCHG+sc`. Two threads, one exchange each, with no release and no data.
  - Group E, release sequence: `RS+rel+rlx`. A release store followed in the same thread by a non-RMW atomic write to the same location, read by an acquire load.
- `run.sh`: runs every test under `rc11.cat` and writes the raw herd7 output to `results/<test>.txt`. It also runs:
  - `LB+rlx` with the `no-thin-air` check skipped (`results/LB+rlx+skip-no-thin-air.txt`);
  - the lock tests `LOCK+xchg-acq+rel` to `LOCK+cas-acq+rel` and the group D tests with RMW checks skipped, as `results/<test>+skip-<checks>.txt`, the checks being joined by `-`. `LOCK3+xchg-acq+rel` is not run with checks skipped: one run takes minutes.
- `results/`: the raw outputs.

## Tool

- herdtools7 7.58, installed with opam. `rc11.cat` is the model shipped with it, in the directory printed by `herd7 -libdir`.
- Its checks are `coherence1`, `coherencermw`, `atomicity`, `SC` and `no-thin-air`. Data races are `undefined_unless empty dr as Dr`, which herd7 reports as `Undef` and `Flag *undef*`.
- The model is selected with `-model rc11.cat`; the default C model of herd7 is `c11_partialSC.cat`.
- A named check is skipped with `-skipcheck <name>`, a list with `-skipchecks <name,..,name>`. No local copy of the model is made.

## Rerun

```sh
HERD7=/path/to/herd7 formal/herd/run.sh
```

`HERD7` defaults to `herd7` on `PATH`. The script exits with status 1 if an output has no `Observation` line, which is the case when herd7 rejects a test. A full run takes about 6.5 minutes, almost all of it for the three-thread `LOCK3+xchg-acq+rel`.

## Correspondence ERN ↔ C11

| ERN (WC5.1) | C litmus test |
|---|---|
| `readShared(l, order)` | `atomic_load_explicit(l, memory_order_…)` |
| `writeShared(l, v, order)` on an `Atomic` leaf | `atomic_store_explicit(l, v, memory_order_…)` |
| RMW (C39) | `atomic_exchange_explicit`, `atomic_compare_exchange_strong_explicit` |
| `read3`, `write3` | ordinary read and write of an `int` |
| `relaxed`, `release`, `acquire`, `acq_rel`, `seq_cst` | the C11 orders of the same name |

## Notes on the tests

- In the herd7 C dialect, `*x` is a non-atomic access whatever the declared type, and only the `atomic_*` calls produce atomic events.
- `MP+*`, `LOCK3+xchg-acq+rel` and `RS+rel+rlx` initialise `r1` to `-1`, so that `r1` has a value when the guarded read does not run.
- In the `LOCK+*` tests, the `exists` clause asks whether both threads take the lock (`r0 = 0` for the exchange tests, `r0 = 1` for the compare-exchange test). A lock that is released can be taken again, so this outcome also covers two successive acquisitions. The group D tests have no release, so there the same outcome means two overlapping acquisitions.
- herd7 rejects `&e` for a local `e` as the expected-value argument of `atomic_compare_exchange_strong_explicit`. `LOCK+cas-acq+rel` passes instead a pointer to a per-thread non-atomic location (`e0`, `e1`), and `r0` is the boolean result of the compare-exchange.
- In `RS+rel+rlx`, the release sequence of `rc11.cat` includes the later non-RMW atomic write of the same thread to the same location. WC5.1 C48 takes the C++20 form instead, where only RMWs extend a release sequence; the tests do not run that form.
