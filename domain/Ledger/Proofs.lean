import Ledger.Statements
namespace Spec

/-! ### Helper lemmas -/

theorem sum_cons (p : Posting) (ps : List Posting) :
    Transaction.sum ⟨p :: ps⟩ = p.amount + Transaction.sum ⟨ps⟩ := rfl

theorem total_append (l₁ l₂ : Ledger) :
    (l₁ ++ l₂).total = l₁.total + l₂.total := by
  induction l₁ with
  | nil => simp [Ledger.total]
  | cons t ts ih => simp only [Ledger.total, List.cons_append, List.foldr] at *; omega

/-- |sum| ≤ 10^12 · length when every amount is in bounds. -/
theorem sum_bound (ps : List Posting) (h : ∀ p ∈ ps, AmountOk p.amount) :
    -(1000000000000 * (ps.length : Int)) ≤ Transaction.sum ⟨ps⟩ ∧
    Transaction.sum ⟨ps⟩ ≤ 1000000000000 * (ps.length : Int) := by
  induction ps with
  | nil => simp [Transaction.sum]
  | cons p ps ih =>
    have hp := h p (by simp)
    have := ih (fun q hq => h q (by simp [hq]))
    rw [sum_cons]
    unfold AmountOk maxAmount at hp
    simp only [List.length_cons]
    omega

theorem inner_bound (a : Account) (ps : List Posting) (h : ∀ p ∈ ps, AmountOk p.amount) :
    -(1000000000000 * (ps.length : Int)) ≤
        ps.foldr (fun p s => if p.account = a then p.amount + s else s) 0 ∧
    ps.foldr (fun p s => if p.account = a then p.amount + s else s) 0 ≤
        1000000000000 * (ps.length : Int) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp := h p (by simp)
    have := ih (fun q hq => h q (by simp [hq]))
    unfold AmountOk maxAmount at hp
    simp only [List.foldr, List.length_cons]
    split <;> omega

theorem balance_bound (a : Account) (l : Ledger) (h : ∀ t ∈ l, InBounds t) :
    -(1000000000000 * (l.postingCount : Int)) ≤ Ledger.balanceOf a l ∧
    Ledger.balanceOf a l ≤ 1000000000000 * (l.postingCount : Int) := by
  induction l with
  | nil => simp [Ledger.balanceOf, Ledger.postingCount]
  | cons t ts ih =>
    have ht := h t (by simp)
    have := ih (fun q hq => h q (by simp [hq]))
    have hi := inner_bound a t.postings ht.2
    simp only [Ledger.balanceOf, Ledger.postingCount, List.foldr] at *
    omega

theorem postingCount_drop (l : Ledger) (k : Nat) :
    Ledger.postingCount (l.drop k) ≤ Ledger.postingCount l := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    cases l with
    | nil => simp
    | cons t ts =>
      have := ih ts
      simp only [List.drop_succ_cons, Ledger.postingCount, List.foldr] at *
      omega

/-! ### Main theorems -/

theorem maxAmountIsTenPow12 : MaxAmountIsTenPow12 := by
  unfold MaxAmountIsTenPow12 maxAmount; decide

theorem txSumFitsInt63 : TxSumFitsInt63 := by
  intro t ht k
  obtain ⟨hlen, hall⟩ := ht
  have hall' : ∀ p ∈ t.postings.drop k, AmountOk p.amount :=
    fun p hp => hall p (List.mem_of_mem_drop hp)
  have hl : (t.postings.drop k).length ≤ 1000 := by
    have := List.length_drop (l := t.postings) (i := k)
    unfold maxPostings at hlen; omega
  have := sum_bound _ hall'
  unfold FitsInt63 int63Min int63Max
  omega

theorem balanceFitsInt63 : BalanceFitsInt63 := by
  intro l a hl k
  obtain ⟨hv, hcount⟩ := hl
  have hin : ∀ t ∈ l.drop k, InBounds t := fun t ht => (hv t (List.mem_of_mem_drop ht)).2
  have hb := balance_bound a (l.drop k) hin
  have hc := postingCount_drop l k
  unfold maxLedgerPostings at hcount
  unfold FitsInt63 int63Min int63Max
  omega

theorem appendKeepsTotalZero : AppendKeepsTotalZero := by
  intro l t hb hz
  rw [total_append]
  have : t.sum = 0 := hb.2
  simpa [Ledger.total, this] using hz

theorem inBounds_iff (p : Posting) : p.inBounds = true ↔ AmountOk p.amount := by
  simp [Posting.inBounds, AmountOk]

theorem validate_iff (t : Transaction) : Transaction.validate t = true ↔ Valid t := by
  simp only [Transaction.validate, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    inBounds_iff, Valid, Balanced, InBounds]
  constructor
  · rintro ⟨⟨⟨h2, h3⟩, h4⟩, h5⟩; exact ⟨⟨h2, h5⟩, h3, h4⟩
  · rintro ⟨⟨h2, h5⟩, h3, h4⟩; exact ⟨⟨⟨h2, h3⟩, h4⟩, h5⟩

theorem validateSound : ValidateSound := fun t h => (validate_iff t).1 h
theorem validateComplete : ValidateComplete := fun t h => (validate_iff t).2 h

theorem ledgerValidIff : LedgerValidIff := by
  intro l
  simp only [Ledger.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    validate_iff, LedgerOk]

end Spec
