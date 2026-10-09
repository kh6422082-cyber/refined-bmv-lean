# 第三方证明来源

本项目的 `RefinedBMV/SchurTriangulation.lean` 来自 Gordon Hsu 的 Apache-2.0 开源 Schur 三角化证明。原版权头保留。

- 上游：[leanprover-community/physlib](https://github.com/leanprover-community/physlib/blob/6bd0b4b99d3d7f05c15b473bed7ccdc115fb0654/Physlib/Mathematics/SchurTriangulation.lean)
- 固定提交：`6bd0b4b99d3d7f05c15b473bed7ccdc115fb0654`
- 原始源码副本：`verification/external_sources/SchurTriangulation.lean.txt`
- 原始源码 SHA256：`efdd028f1b66f37a84291db071c820ecaf204927244172d1d3ef161a6b3cf245`
- 兼容性修改：删除已被 mathlib 提供的重复 `Matrix.IsUpperTriangular` 缩写；更新 orthogonalProjection 和 Bool.cond 的弃用名称。
- Apache-2.0 许可全文：`verification/external_sources/Apache-2.0_LICENSE.txt`（标准许可文本来自本机 mathlib 的 LICENSE）。
- 项目在本机 Lean 4.34.0 重新编译该证明，并对 `Matrix.schur_triangulation` 执行公理依赖审计。

`verification/external_sources` 中 QICLean/QIQT-H 的树清单及其他 `.txt` 文件仅用于寻找解析基础；本项目没有把这些文件导入为证明依赖，也没有把网站的验证状态视为本论文的证明。
