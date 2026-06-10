import VersoBlog
import Mathlib.Data.Nat.Prime.Infinite
open Verso Genre Blog

#doc (Page) "Tau Ceti" =>

```leanInit maths
```

```lean maths
-- There are infinitely many primes: for every `n`, some prime `p ≥ n` exists.
theorem infinitude_of_primes (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime :=
  Nat.exists_infinite_primes n
```
