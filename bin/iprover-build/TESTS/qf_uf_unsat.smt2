(declare-sort A 0)

(declare-const a A) 
(declare-const b A) 
(declare-const c A)
 
(declare-fun g (A) A)
(declare-fun f (A A) A)

(assert (= a c))
(assert (= a b))

;*
; c != b
;(assert (not (= c b)))

;* g(c) = c
;(assert (= (g c) c))

; ~(g(g(a)) = b)
; (assert (not (= (g (g a)) b)))


;*  (f(c,a) = c) 

(assert (= (f c a) c))

;* ~(f(c,a) = f(b,b))

;(assert (not (= (f a c) (f b b))))

(assert (not (= (f a c) b)))

(check-sat)
;(get-model)


