import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive ContextFreeLanguageUp : Type where
  | mk
      (grammar nonterminal terminal production derivation yield membership transport replay
        provenance localName boundary : _root_.BEDC.FKernel.Hist.BHist) :
      ContextFreeLanguageUp

end BEDC.Derived
