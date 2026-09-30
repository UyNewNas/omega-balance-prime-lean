# Lean cache scope: narrow efficiency change

## Observed evidence

The exact successful batch verification job
[109802239984](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36689237049/job/109802239984)
restored an approximately 4079 MB cache under key
`lean-Linux-eacf1c0a469c4f0c32719f294c082fd8ff6476f90b453569a6c0ced4b4ab6fc1`.
It finished the full verification shortly after restoration. By contrast,
[master run 36683869679](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36683869679)
explicitly missed that key and required the long cold build before saving it.

GitHub isolates branch and PR-merge caches; other branches can fall back to the
default branch, but the default branch cannot consume child-branch caches.
Its documented default repository storage limit is 10 GB, with access-ordered
eviction. Multiple approximately 4 GB branch copies therefore plausibly cause
cache churn. Actual eviction IDs and this repository's configured quota were
not verified: the connected public fetch interface does not expose cache inventory.
This report treats churn as an inference, not a confirmed diagnosis.
[Official access and eviction reference](https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching)

## Exact change

- Restore the same paths and exact same key everywhere, using
  `actions/cache/restore@v4`
- Save only after all verification and artifact-upload steps succeed, on a
  nonempty default branch name with a branch ref and push/manual trigger
- Skip saving an exact cache hit; reuse the restore action's
  `cache-primary-key` output rather than recomputing a key after dependency preparation
- Feature branches, PR merge refs, tags, failed runs and missing-key/default-name
  contexts do not save another copy
- A cache miss still runs every existing fetch, producer, library, regression,
  source, pin and axiom step; no build is conditional on a cache hit

The official v4 action schemas and documentation were read:
[restore action](https://github.com/actions/cache/blob/v4/restore/action.yml),
[save action](https://github.com/actions/cache/blob/v4/save/action.yml),
[restore documentation](https://github.com/actions/cache/blob/v4/restore/README.md),
[save documentation](https://github.com/actions/cache/blob/v4/save/README.md).
The restore action has no automatic save post-step; the save action accepts
the resolved primary key. Both remain the same existing official v4 action family.

Paths stay `~/.elan` and `.lake`; triggers, contents-read permission, timeout,
concurrency, all proof/audit commands and their conditions stay unchanged.
No quota, billing, repository permission, security-mode, or dependency-pin setting
is altered. No existing cache is deleted. A missing initial mainline cache merely
uses the existing cold-build fallback; the next fully successful mainline run can
populate it. Active older branches retain their previous workflow until updated.

## Validation and acceptance

YAML was parsed, and every non-cache step was compared against the baseline
workflow value-for-value. The exact new Boolean guard was parsed into a restricted
Boolean AST and checked across 432 normal event/ref/status/key/output combinations.
Only four default-branch successful cache-miss combinations save.
The machine-readable result is
[lean_cache_scope_validation.json](lean_cache_scope_validation.json).

This is configuration/source validation, not a claim that Actions has run it.
Before merge, the exact candidate must pass all existing CI gates and independent
workflow review. After merge, observe a real default-branch run: restoration and all
proof gates must still run, and saving should occur only for a miss. An exact hit
properly skips saving, so a hit alone does not demonstrate a newly uploaded cache.
