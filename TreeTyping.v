(** * Umbrella module for the core development.

    [From TreeTyping Require Import TreeTyping.] imports tree calculus
    (tree.v), the typing programs (typing.v), soundness (soundness.v), and
    the booleans (booleans.v). *)
From TreeTyping Require Export tree typing soundness booleans.
