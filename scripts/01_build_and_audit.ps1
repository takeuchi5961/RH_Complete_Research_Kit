$ErrorActionPreference = "Stop"
$root = Split-Path -Parent $PSScriptRoot
Set-Location $root

Write-Host "== Build ==" -ForegroundColor Cyan
lake build | Tee-Object -FilePath .\build_log.txt

Write-Host "== Placeholder scan ==" -ForegroundColor Cyan
$placeholderLog = Join-Path $root "no_placeholder_check.txt"
New-Item -Path $placeholderLog -ItemType File -Force | Out-Null
$hits = Get-ChildItem .\RHLean\*.lean |
  Select-String -Pattern '^\s*axiom\b','\bsorry\b','\badmit\b'
if ($null -ne $hits -and $hits.Count -gt 0) {
  $hits | Set-Content -Path $placeholderLog -Encoding utf8
} else {
  "" | Set-Content -Path $placeholderLog -Encoding utf8
}

Write-Host "== Axiom dependency audit ==" -ForegroundColor Cyan
@'
import RHLean
#print axioms RHLean.zeta_zero_iff_geo_zero_on_critical
#print axioms RHLean.bridge_forward
#print axioms RHLean.bridge_reverse_with_cover
'@ | Set-Content .\AxiomAudit.lean -Encoding utf8 -NoNewline
lake env lean .\AxiomAudit.lean | Tee-Object -FilePath .\axiom_audit_log.txt

Write-Host "== Hashes ==" -ForegroundColor Cyan
Get-FileHash .\RHLean\*.lean -Algorithm SHA256 | Tee-Object -FilePath .\sha256_lean_files.txt

Write-Host "Done." -ForegroundColor Green
