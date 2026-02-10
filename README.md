# RH Complete Research Kit v3

このキットは、あなたの現在の流れ（Lean再ビルド → 監査 → ZIP化 → 数値記録CSV）を**一発実行**できるように整理した版です。

## 同梱内容
- Leanプロジェクト（`RHLean/`, `RHLean.lean`）
- 監査スクリプト
  - `scripts/01_build_and_audit.ps1`
  - `scripts/02_make_audit_bundle.ps1`
- 数値記録スクリプト
  - `scripts/03_export_abcd_overlap.ps1`
- 一括実行スクリプト
  - `scripts/00_run_all.ps1`
- 補助可視化 `visual/abc.html`

## 実行手順（PowerShell）
```powershell
Set-Location "C:\Users\banbo\Desktop\RH_Complete_Research_Kit_v3"
elan override set leanprover/lean4:v4.28.0-rc1
lake update
lake exe cache get

# これ1本で: CSV出力 → build/audit → ZIP作成
powershell -ExecutionPolicy Bypass -File .\scripts\00_run_all.ps1
```

## 個別実行したい場合
```powershell
powershell -ExecutionPolicy Bypass -File .\scripts\03_export_abcd_overlap.ps1
powershell -ExecutionPolicy Bypass -File .\scripts\01_build_and_audit.ps1
powershell -ExecutionPolicy Bypass -File .\scripts\02_make_audit_bundle.ps1
```

## 生成物
- `data/abcd_overlap_0p1_to_0p9_step0p01.csv`
- `build_log.txt`
- `no_placeholder_check.txt`（0件でも空ファイルを必ず作成）
- `axiom_audit_log.txt`
- `sha256_lean_files.txt`
- `RHLean_AuditBundle_v1.zip`
- `RELEASE_NOTE.txt`

## 重要メモ
- PowerShellに貼るのは**コマンドだけ**。プロンプト文字列（`PS C:\...>`）を一緒に貼るとエラーになります。
- `#print axioms` に `propext, Classical.choice, Quot.sound` が出るのは、通常のLean/Mathlib依存の表示です（`axiom/sorry/admit` 検査とは別軸）。
