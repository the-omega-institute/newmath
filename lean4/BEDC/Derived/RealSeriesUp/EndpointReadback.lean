import BEDC.Derived.RealSeriesUp.RootTailFactorization

namespace BEDC.Derived.RealSeriesUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RealSeriesEndpointReadback
    {T S W Q D M E TS TSW TSWQ TSWQD TSWQDM endpoint : BHist} :
    Cont T S TS →
      Cont TS W TSW →
        Cont TSW Q TSWQ →
          Cont TSWQ D TSWQD →
            Cont TSWQD M TSWQDM →
              Cont TSWQDM E endpoint →
                UnaryHistory T →
                  UnaryHistory S →
                    UnaryHistory W →
                      UnaryHistory Q →
                        UnaryHistory D →
                          UnaryHistory M →
                            UnaryHistory E →
                              ∃ beforeSeal : BHist,
                                Cont TSWQD M beforeSeal ∧ Cont beforeSeal E endpoint ∧
                                  UnaryHistory beforeSeal ∧ UnaryHistory endpoint ∧
                                    hsame beforeSeal TSWQDM := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro hTS hTSW hTSWQ hTSWQD hTSWQDM hEndpoint
  intro TUnary SUnary WUnary QUnary DUnary MUnary EUnary
  have TSUnary : UnaryHistory TS :=
    unary_cont_closed TUnary SUnary hTS
  have TSWUnary : UnaryHistory TSW :=
    unary_cont_closed TSUnary WUnary hTSW
  have TSWQUnary : UnaryHistory TSWQ :=
    unary_cont_closed TSWUnary QUnary hTSWQ
  have TSWQDUnary : UnaryHistory TSWQD :=
    unary_cont_closed TSWQUnary DUnary hTSWQD
  have beforeSealUnary : UnaryHistory TSWQDM :=
    unary_cont_closed TSWQDUnary MUnary hTSWQDM
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed beforeSealUnary EUnary hEndpoint
  exact
    ⟨TSWQDM, hTSWQDM, hEndpoint, beforeSealUnary, endpointUnary,
      hsame_refl TSWQDM⟩

end BEDC.Derived.RealSeriesUp
