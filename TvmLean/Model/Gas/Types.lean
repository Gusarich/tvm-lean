import TvmLean.Model.Stack.Stack
import TvmLean.Model.Cell.Cell

namespace TvmLean

structure CallFrame where
  savedStack : Stack
  retArgs : Int
  deriving Repr

def CallFrame.identity : CallFrame := { savedStack := #[], retArgs := -1 }

structure GasLimits where
  gasMax : Int
  gasLimit : Int
  gasCredit : Int
  gasRemaining : Int
  gasBase : Int
  deriving Repr

def GasLimits.infty : Int := (Int.ofNat (1 <<< 63)) - 1

def GasLimits.default : GasLimits :=
  { gasMax := GasLimits.infty
    gasLimit := GasLimits.infty
    gasCredit := 0
    gasRemaining := GasLimits.infty
    gasBase := GasLimits.infty }

def GasLimits.ofLimit (limit : Int) : GasLimits :=
  { gasMax := GasLimits.infty
    gasLimit := limit
    gasCredit := 0
    gasRemaining := limit
    gasBase := limit }

def GasLimits.ofLimits (limit max credit : Int) : GasLimits :=
  let base : Int := limit + credit
  { gasMax := max
    gasLimit := limit
    gasCredit := credit
    gasRemaining := base
    gasBase := base }

def GasLimits.gasConsumed (g : GasLimits) : Int :=
  g.gasBase - g.gasRemaining

def GasLimits.changeBase (g : GasLimits) (newBase : Int) : GasLimits :=
  { g with gasRemaining := g.gasRemaining + (newBase - g.gasBase), gasBase := newBase }

def GasLimits.changeLimit (g : GasLimits) (newLimit : Int) : GasLimits :=
  let limit0 : Int := if newLimit < 0 then 0 else newLimit
  let limit : Int := if limit0 > g.gasMax then g.gasMax else limit0
  let g' : GasLimits := { g with gasCredit := 0, gasLimit := limit }
  g'.changeBase limit

def GasLimits.consume (g : GasLimits) (amount : Int) : GasLimits :=
  { g with gasRemaining := g.gasRemaining - amount }

structure CommittedState where
  c4 : Cell
  c5 : Cell
  committed : Bool
  deriving Repr

def CommittedState.empty : CommittedState :=
  { c4 := Cell.empty, c5 := Cell.empty, committed := false }

end TvmLean
