(set-logic HORN)


(declare-fun p
    ( Int Int ) Bool
)

(assert
    ( =>
        true
        (p 0 0)
    )
)

(assert
    (forall
        ( (x Int) (y Int) )
        ( =>
            (p x (+ x y))
            (p (+ x 1) (+ x y))
        )
    )
)

(assert
    (forall
        ( (x Int) (y Int) )
        ( =>
            (and (p x y) (> y 0))
            false
        )
    )
)

(check-sat)
(get-model)