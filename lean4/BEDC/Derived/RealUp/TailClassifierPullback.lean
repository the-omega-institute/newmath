import BEDC.Derived.RealUp.ScopedFiniteWindowReadSurface

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RegseqratTailClassifierPullbackUniqueness
    {dyadic regseq stream rat endpoint ledger selected0 selected1 candidate witness0
      witness1 : BHist} :
    UnaryHistory dyadic ->
    UnaryHistory regseq ->
    UnaryHistory rat ->
    Cont dyadic regseq stream ->
    Cont stream rat endpoint ->
    Cont endpoint stream ledger ->
    Cont selected0 candidate witness0 ->
    Cont selected1 candidate witness1 ->
    hsame selected0 selected1 ->
      UnaryHistory stream ∧ UnaryHistory endpoint ∧ UnaryHistory ledger ∧
        hsame witness0 witness1 := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro dyadicUnary regseqUnary ratUnary streamCont endpointCont ledgerCont selected0Candidate
    selected1Candidate sameSelected
  obtain ⟨streamUnary, endpointUnary, ledgerUnary, _streamSame, _endpointSame,
    _ledgerSame⟩ :=
    RealupScopedFiniteWindowReadSurface dyadicUnary regseqUnary ratUnary streamCont
      endpointCont ledgerCont
  have sameWitness : hsame witness0 witness1 :=
    cont_respects_hsame sameSelected (hsame_refl candidate) selected0Candidate selected1Candidate
  exact ⟨streamUnary, endpointUnary, ledgerUnary, sameWitness⟩

end BEDC.Derived.RealUp
