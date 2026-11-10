$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    $lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
    $lakeExe = if ($lakeCommand) { $lakeCommand.Source } else {
        Join-Path $env:USERPROFILE '.elan/bin/lake.exe'
    }
    if (-not (Test-Path -LiteralPath $lakeExe)) {
        throw 'Install elan first: https://lean-lang.org/install/manual/'
    }
    $sources = Get-ChildItem -LiteralPath $PSScriptRoot -Filter '*.lean' -Recurse |
        Where-Object { $_.FullName -notmatch '[\\/]\.lake[\\/]' }
    $unfinished = $sources | Select-String -Pattern '\b(sorry|admit|axiom)\b'
    if ($unfinished) { throw "Unfinished proof or axiom declaration: $unfinished" }
    & $lakeExe build
    if ($LASTEXITCODE -ne 0) { throw 'Lean build failed.' }
    $audit = & $lakeExe env lean Audit.lean 2>&1
    $auditExit = $LASTEXITCODE
    $audit | ForEach-Object { Write-Output $_ }
    if ($auditExit -ne 0) { throw 'Lean axiom audit failed.' }
    if ($audit -match 'sorryAx') { throw 'An audited theorem depends on sorryAx.' }
    # Every named project theorem must appear in the environment audit.
    $expected = @($sources | Select-String -Pattern '^\s*(?:theorem|lemma)\s+([A-Za-z_][A-Za-z_0-9]*)' |
        ForEach-Object { $_.Matches[0].Groups[1].Value })
    foreach ($name in $expected) {
        if (-not ($audit -match ('CHECKED BrownRadial\.' + [regex]::Escape($name) + ':'))) {
            throw "Theorem missing from audit imports: $name"
        }
    }
    $record = [ordered]@{
        checkedAtUtc = [DateTime]::UtcNow.ToString('o')
        namedTheorems = $expected.Count
        status = 'PASS'
        scope = 'Lean declarations only; full paper verification is incomplete'
        files = @($sources | ForEach-Object {
            @{ path = $_.FullName.Substring($PSScriptRoot.Length + 1); sha256 = (Get-FileHash -LiteralPath $_.FullName -Algorithm SHA256).Hash }
        })
        paperSha256 = (Get-FileHash -LiteralPath '../paper/radial-tests.tex' -Algorithm SHA256).Hash
        audit = @($audit | ForEach-Object { "$_" })
    }
    $record | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath 'verification.json' -Encoding UTF8
} finally {
    Pop-Location
}
