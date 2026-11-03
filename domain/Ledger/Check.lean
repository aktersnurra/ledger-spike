import Ledger.Proofs
/-!
Proof gate. Each statement is re-ascribed to its proof (so a proof of a
different/weaker statement cannot slip in), then axioms are printed. Allowed:
`propext`, `Classical.choice`, `Quot.sound`. `scripts/proof-gate.sh` checks that.
-/
namespace Spec
example : MaxAmountIsTenPow12 := maxAmountIsTenPow12
example : TxSumFitsInt63 := txSumFitsInt63
example : BalanceFitsInt63 := balanceFitsInt63
example : AppendKeepsTotalZero := appendKeepsTotalZero
example : ValidateSound := validateSound
example : ValidateComplete := validateComplete
example : LedgerValidIff := ledgerValidIff

#print axioms maxAmountIsTenPow12
#print axioms txSumFitsInt63
#print axioms balanceFitsInt63
#print axioms appendKeepsTotalZero
#print axioms validateSound
#print axioms validateComplete
#print axioms ledgerValidIff
end Spec
