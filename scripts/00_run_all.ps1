param(
  [string]$Root = (Get-Location).Path
)

$ErrorActionPreference = "Stop"
Set-Location $Root

# その場だけ実行許可
Set-ExecutionPolicy -Scope Process -ExecutionPolicy Bypass -Force

Write-Host "== Build & Audit ==" -ForegroundColor Cyan
& "$Root\scripts\01_build_and_audit.ps1" -Root $Root

if (-not (Test-Path "$Root\no_placeholder_check.txt")) {
  New-Item -Path "$Root\no_placeholder_check.txt" -ItemType File -Force | Out-Null
}

Write-Host "== Bundle ==" -ForegroundColor Cyan
& "$Root\scripts\02_make_audit_bundle.ps1" -Root $Root -OutZip "RHLean_AuditBundle_v1.zip"

$zip = Get-Item "$Root\RHLean_AuditBundle_v1.zip"
$hash = (Get-FileHash $zip.FullName -Algorithm SHA256).Hash

@"
Release: RHLean_AuditBundle_v1
SHA256: $hash
Audit logs: build_log.txt / axiom_audit_log.txt / sha256_lean_files.txt
"@ | Set-Content "$Root\RELEASE_NOTE.txt" -Encoding utf8

Write-Host "ZIP : $($zip.FullName)" -ForegroundColor Green
Write-Host "SHA : $hash" -ForegroundColor Green
Write-Host "NOTE: $Root\RELEASE_NOTE.txt" -ForegroundColor Green
