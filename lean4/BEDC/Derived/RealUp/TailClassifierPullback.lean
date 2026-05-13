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

theorem RegseqratTailClassifierExactness
    {stream0 stream1 regseq0 regseq1 dyadic0 dyadic1 endpoint0 endpoint1 ledger0 ledger1
      tail0 tail1 : BHist} :
    UnaryHistory stream0 ->
    UnaryHistory regseq0 ->
    UnaryHistory dyadic0 ->
    hsame stream0 stream1 ->
    hsame regseq0 regseq1 ->
    hsame dyadic0 dyadic1 ->
    Cont stream0 regseq0 endpoint0 ->
    Cont stream1 regseq1 endpoint1 ->
    Cont endpoint0 dyadic0 ledger0 ->
    Cont endpoint1 dyadic1 ledger1 ->
    Cont ledger0 stream0 tail0 ->
    Cont ledger1 stream1 tail1 ->
      UnaryHistory endpoint0 ∧ UnaryHistory endpoint1 ∧ UnaryHistory ledger0 ∧
        UnaryHistory ledger1 ∧ hsame tail0 tail1 := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro streamUnary regseqUnary dyadicUnary sameStream sameRegseq sameDyadic endpointCont0
    endpointCont1 ledgerCont0 ledgerCont1 tailCont0 tailCont1
  have streamUnary1 : UnaryHistory stream1 :=
    unary_transport streamUnary sameStream
  have regseqUnary1 : UnaryHistory regseq1 :=
    unary_transport regseqUnary sameRegseq
  have dyadicUnary1 : UnaryHistory dyadic1 :=
    unary_transport dyadicUnary sameDyadic
  have endpointUnary0 : UnaryHistory endpoint0 :=
    unary_cont_closed streamUnary regseqUnary endpointCont0
  have endpointUnary1 : UnaryHistory endpoint1 :=
    unary_cont_closed streamUnary1 regseqUnary1 endpointCont1
  have ledgerUnary0 : UnaryHistory ledger0 :=
    unary_cont_closed endpointUnary0 dyadicUnary ledgerCont0
  have ledgerUnary1 : UnaryHistory ledger1 :=
    unary_cont_closed endpointUnary1 dyadicUnary1 ledgerCont1
  have sameEndpoint : hsame endpoint0 endpoint1 :=
    cont_respects_hsame sameStream sameRegseq endpointCont0 endpointCont1
  have sameLedger : hsame ledger0 ledger1 :=
    cont_respects_hsame sameEndpoint sameDyadic ledgerCont0 ledgerCont1
  have sameTail : hsame tail0 tail1 :=
    cont_respects_hsame sameLedger sameStream tailCont0 tailCont1
  exact ⟨endpointUnary0, endpointUnary1, ledgerUnary0, ledgerUnary1, sameTail⟩

end BEDC.Derived.RealUp
