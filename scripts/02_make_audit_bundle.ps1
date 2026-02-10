$ErrorActionPreference = "Stop"
$root = Split-Path -Parent $PSScriptRoot
Set-Location $root

# no_placeholder_check.txt は 0 件でも必須ログとして空ファイルを許可
if (-not (Test-Path .\no_placeholder_check.txt)) {
  New-Item -Path .\no_placeholder_check.txt -ItemType File -Force | Out-Null
}

$files = @(
  "RHLean",
  "RHLean.lean",
  "lakefile.toml",
  "lean-toolchain",
  "build_log.txt",
  "no_placeholder_check.txt",
  "axiom_audit_log.txt",
  "sha256_lean_files.txt"
)

# 任意: 数値記録CSVがあれば同梱
if (Test-Path .\data\abcd_overlap_0p1_to_0p9_step0p01.csv) {
  $files += "data\\abcd_overlap_0p1_to_0p9_step0p01.csv"
}

$missing = $files | Where-Object { -not (Test-Path $_) }
if ($missing.Count -gt 0) {
  Write-Host "Missing files:" -ForegroundColor Red
  $missing | ForEach-Object { Write-Host " - $_" -ForegroundColor Red }
  throw "Run scripts\\01_build_and_audit.ps1 first."
}

$zip = ".\RHLean_AuditBundle_v1.zip"
Compress-Archive -Path $files -DestinationPath $zip -Force
Get-FileHash $zip -Algorithm SHA256
Get-Item $zip | Format-List LastWriteTime,Length,Name
