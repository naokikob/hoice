(set-logic HORN)


(declare-fun main@_4
    ( Bool Int Int Int Int ) Bool
)
 
; C #0
(assert
    (forall
        ( (D Int) (H Bool) (I Int) (K Int) (L Int) )
        ( =>
            (and
                (>= (+ (* (- 1) L) K) 0)
                (main@_4 H I D (+ K (ite (>= (+ D (* (- 1) I)) 1) 1 (- 1))) L)
            )
            (main@_4 H I (+ 1 D) K L)
        )
    )
)
 
; C #1
(assert
    (forall ( (E Int) )
        (=>
            (and (>= E 0) true)
            (main@_4 true E 0 0 0)
        )
    )
)
 
; C #2
(assert
    (forall( (D Int) (E Int) (I Int) (J Int) )
        ( =>
            (and
                (>= (+ E (* (- 1) D)) 1) (>= (+ J (* (- 2) I)) 3)
                (main@_4 true I J (+ D (ite (>= (+ J (* (- 1) I)) 1) 1 (- 1))) E)
            )
            false
        )
    )
)
(check-sat)
(get-model)