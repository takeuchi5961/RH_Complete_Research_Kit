# RH Complete Research Kit v6

リーマン予想（Riemann Hypothesis）の研究と検証のための包括的なツールキット。Lean 4 での形式検証、Python での数値計算、インタラクティブな可視化ツールを統合。

## 📁 プロジェクト構造

\\\
RH_Complete_Research_Kit_v6/
├── RHLean/                    # Lean 4 形式検証コード
├── python/                    # Python 数値計算スクリプト
├── visualization/             # インタラクティブ HTML 可視化
├── data/                      # 計算結果データ（JSON）
├── docs/                      # ドキュメント
├── reproducibility/           # 再現性検証資料
├── submission_docs/           # 論文投稿用資料
├── scripts/                   # ビルド・監査スクリプト
├── audit/                     # Axiom 監査記録
├── images/                    # 図表・画像
└── archive/                   # 古いバージョン
\\\

## 🚀 クイックスタート

### 必要環境

- **Lean 4** (v4.14.0-rc1 以上)
- **Python 3.8+** (mpmath, numpy, matplotlib)
- **PowerShell** (Windows)

### ビルド手順

\\\powershell
lake build                           # Lean プロジェクトをビルド
.\scripts\00_run_all.ps1             # すべて自動実行
.\scripts\01_build_and_audit.ps1     # ビルドと監査のみ
\\\

## 📊 主要コンポーネント

### 1. Lean 4 形式検証 (RHLean/)

| ファイル | 内容 |
|---------|------|
| RhBridge.lean | メイン証明ファイル |
| ABCDGeometry.lean | ABCD 幾何モデル |
| DeltaCore.lean | Delta 関数の定義 |

### 2. Python 数値検証 (python/)

- generate_evidence.py - 数値エビデンス生成
- visualize_rh_geometry.py - 幾何モデル可視化
- zeta_spiral.py - ゼータ螺旋シミュレーション

### 3. 可視化ツール (visualization/)

ブラウザで HTML ファイルを直接開いて使用：
- 01_Global_Zeta_3D.html - 3D ゼータ関数
- 02_Zeta_Exact_Zero_Focus.html - ゼロ点拡大
- 03_Vector_Core_Dynamics.html - ベクトル場
- GeometricModelABCD.html - ABCD 幾何モデル

## 🔬 検証結果

- **data/riemann_zeros_*.json** - リーマンゼロ点データ
- **audit/axiom_audit_log.txt** - Axiom 使用状況

## ⚠️ 注意事項

1. **.lake/ フォルダー**: Git 管理対象外（ビルド成果物）
2. **Sorry の使用**: RhBridge.lean に 2 箇所あり（証明未完）
3. **数値精度**: mpmath で 50 桁精度を使用

## 📄 ライセンス

MIT License

## 👤 著者

竹内 寛樹 (Hiroki Takeuchi)  
大分県在住 数学研究者

---

**バージョン:** v6 | **最終更新:** 2025年2月
