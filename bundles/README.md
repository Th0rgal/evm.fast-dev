# Wave 8 transfer bundles

Incremental git bundles for the evm-fast-pilot Wave 8 campaign.

- `r32_inc.bundle`: `origin/wave8/r32-bundle` = `d0bcd295677ce04f91ecf3ec7adc1d05b43816ec`
  (incremental over `b76bc1b37` = `origin/wave8/cutover-rehearsal` and `d26bd0205`
  = `origin/wave8/wip/wk-ptx-phase4-r21`).
  SHA-256: `9422a39b66b18bee51a7ffcd958ded493412e642b97993308a2e7c04bf129f68`

Import (inside a clone of the private pilot repo):

```bash
sha256sum r32_inc.bundle
git bundle verify r32_inc.bundle
git fetch r32_inc.bundle 'refs/remotes/origin/wave8/r32-bundle:refs/remotes/origin/wave8/r32-bundle'
```
