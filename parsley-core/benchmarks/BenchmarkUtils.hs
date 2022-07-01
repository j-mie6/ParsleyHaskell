module BenchmarkUtils where

import Gauge.Main         (Benchmark, defaultMainWith)
import Gauge.Main.Options (Config(displayMode), defaultConfig, DisplayMode(Condensed))

condensedMain :: [Benchmark] -> IO ()
condensedMain = defaultMainWith (defaultConfig {displayMode = Condensed})
