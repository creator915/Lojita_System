import Test.KernelTaboos.Harness
import Test.KernelTaboos.HistoricalRepros
import Test.KernelTaboos.CommunitySuite
import Test.KernelTaboos.SoundnessGates

def main : IO Unit := do
  Lojita.Kernel.initKernelLimits
  let rssStart ← Lojita.Kernel.readProcessRssKB
  let t0 ← IO.monoNanosNow
  Lojita.Kernel.preload
  try
    Test.KernelTaboos.HistoricalRepros.runAll
    Test.KernelTaboos.CommunitySuite.runAll
    Test.KernelTaboos.SoundnessGates.runAll
    let totalMs := ((← IO.monoNanosNow) - t0) / 1000000
    let rssEnd ← Lojita.Kernel.readProcessRssKB
    IO.println "=================================================================="
    IO.println s!"ALL KERNEL TABOO & SOUNDNESS SUITES PASSED (0 crashes, 0 false positives)"
    IO.println s!"Total wall time: {totalMs} ms | RSS start: {rssStart / 1024} MiB -> end: {rssEnd / 1024} MiB"
    IO.println "=================================================================="
  finally
    Lojita.Kernel.close
