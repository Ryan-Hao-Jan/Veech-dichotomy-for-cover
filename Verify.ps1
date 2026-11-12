$ErrorActionPreference = 'Stop'
$verificationDir = Join-Path $PSScriptRoot 'verification'
New-Item -ItemType Directory -Force -Path $verificationDir | Out-Null
Push-Location $PSScriptRoot
try {
    & lake build *>&1 | Tee-Object -FilePath (Join-Path $verificationDir 'build.log')
    if ($LASTEXITCODE -ne 0) {
        throw 'Lean project build failed.'
    }
    & lake env lean -DwarningAsError=true -DautoImplicit=false CheckMainTheorem.lean *>&1 |
        Tee-Object -FilePath (Join-Path $verificationDir 'main-theorem.log')
    if ($LASTEXITCODE -ne 0) {
        throw 'Exact main theorem replay failed.'
    }
    & lake env lean -DwarningAsError=true -DautoImplicit=false CheckAxioms.lean *>&1 |
        Tee-Object -FilePath (Join-Path $verificationDir 'axiom-audit.log')
    if ($LASTEXITCODE -ne 0) {
        throw 'Transitive axiom audit failed.'
    }
    Write-Output 'Verification passed for the exact paper main theorem and all transitive project dependencies.'
}
finally {
    Pop-Location
}
