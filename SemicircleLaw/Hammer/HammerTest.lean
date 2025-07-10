import Mathlib.Init
import Hammer

-- Setting `aesopPremises` and `autoPremises` to 0 to bypass premise selection
-- which is slow on its first uncached invocation
example : True := by
  hammer {aesopPremises := 0, autoPremises := 0}
