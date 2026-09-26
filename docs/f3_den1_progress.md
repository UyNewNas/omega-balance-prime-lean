# DEN-1 progress

PR #22 contains the candidate partial-summation bridge from weighted AP-PNT to unweighted fixed-residue prime counts, ending at `f3PrimeAPCountingReal_normalized_tendsto`.

The first exact-head build exposed a real Lean 4.34 compatibility failure inside the pinned ANT source. A minimal upstream compatibility commit adds an explicit real binder annotation; the consumer is pinned to that exact commit and is being revalidated. No DEN density theorem is marked complete before exact-head build and audits pass.
