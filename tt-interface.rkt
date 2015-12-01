#lang racket/gui
(require "tt.rkt")
(require mrlib/hierlist)
(require racket/exn)

(provide (all-defined-out))

;;;; Utilities
(define/contract (maybe-set-box! box val)
  (-> (or/c (box/c any/c) false/c)
      any/c
      void?)
  (when box (set-box! box val)))


(define context/c
  (listof (list/c symbol?
                  (or/c list? symbol?))))

(define step-status/c
  (or/c (list/c 'incomplete)
        (list/c 'done term?)
        (list/c 'refined (-> (listof term?) term?))
        (list/c 'error exn:fail?)))


;;;; Model classes
(define proof-step-observer<%>
  (interface ()
    [notify-change (->m any/c any/c)]))

(define/contract proof-step%
  (class/c (init-field
            [context context/c]
            [goal term?]
            [parent (or/c #f (is-a?/c proof-step%))])
           (field [tactic-text string?]
                  [status step-status/c]
                  [subgoals (listof (is-a?/c proof-step%))]
                  [observers (listof (is-a?/c proof-step-observer<%>))])
           [get-sequent (->m sequent?)]
           [add-observer (->m (is-a?/c proof-step-observer<%>) void?)]
           [remove-observer (->m (is-a?/c proof-step-observer<%>) void?)]
           [update-observers (->m void?)]
           [update-parent-status (->m void?)])
  (class object%
    (init-field context goal parent)
    (field [tactic-text ""]
           [status '(incomplete)]
           [subgoals empty]
           [observers empty])

    (super-new)

    (define/public (update-parent-status)
      (match status
        [(list 'incomplete) (void)]
        [(list 'error exn) (void)]
        [(list 'done _)
         (when parent
           (send parent update-parent-status))]
        [(list 'refined ext)
         (when (for/and ([g subgoals])
                 (equal? (car (get-field status g))
                         'done))
           (set! status
                 (list 'done
                       ;; perform extraction of the subtree
                       (ext (for/list ([g subgoals])
                              (cadr (get-field status g))))))
           (update-observers)
           (when parent (send parent update-parent-status)))]))

    (define/public (remove-observer observer)
      (set! observers (remq observer observers)))
    (define/public (add-observer observer)
      (when (not (memq observer observers))
        (set! observers (cons observer observers))))
    (define/public (update-observers)
      (for ([o observers])
        (send o notify-change this)))

    (define/public (get-sequent)
      (⊢ context goal))))


(define (unrefined-proof-step? step)
  (and (is-a? step proof-step%)
       (member (car (get-field status step)) '(incomplete error))))

(define/contract (sequent->proof-step sequent #:parent [parent #f])
  (->* (sequent?)
       (#:parent (or/c #f (is-a?/c proof-step%)))
       (is-a?/c proof-step%))
  (match sequent
    [(⊢ ctxt goal)
     (new proof-step%
          [context ctxt]
          [goal goal]
          [parent parent])]))


;;;; View stuff

;;; A widget for viewing a list of hypotheses
(define/contract hypothesis-list%
  (class/c (init [hypotheses context/c]))
  (class vertical-panel%
    (init-field parent hypotheses)
    (super-new [parent parent]
               [alignment '(left top)]
               [stretchable-height #f])
    (for ([hyp hypotheses]
          [i (range (- (length hypotheses) 1) -1 -1)])
      (new message%
           [parent this]
           [label (format "~a.  ~a : ~a" i (car hyp) (cadr hyp))]))))

;;; A widget for editing a particular proof goal
(define/contract proof-goal-editor-panel%
  (class/c
   [set-proof-step (->m (or/c #f (is-a?/c proof-step%))
                        void?)]
   [get-proof-step (->m (or/c #f (is-a?/c proof-step%)))])
  (class* vertical-panel% (proof-step-observer<%>)
    (init-field parent)

    (inherit/super change-children)

    (super-new [parent parent]
               [alignment '(left top)]
               [stretchable-height #f])

    ;; the underlying model object
    (define proof-step #f)

    (define/public (get-proof-step) proof-step)
    (define/public (set-proof-step new-step)
      (when proof-step (send proof-step remove-observer this))
      (set! proof-step new-step)
      (when proof-step (send proof-step add-observer this))
      (update-step-display)
      (void))

    (define (update-step-display)
      (change-children (lambda (_) empty))
      (if (not proof-step)
          (new message% [parent this] [label "No selected goal"])
          (let* ((hyps (reverse (get-field context proof-step)))
                 (goal (get-field goal proof-step))
                 (hyp-list (new hypothesis-list%
                                [parent this]
                                [hypotheses hyps]))
                 (goal-panel (new horizontal-panel%
                                  [parent this]
                                  [alignment '(left top)]
                                  [stretchable-height #f]))
                 (turnstile (new message%
                                 [parent goal-panel]
                                 [label "⊢ "]))
                 (extract (new text-field%
                               [parent goal-panel]
                               [label #f]
                               [init-value
                                (match (get-field status proof-step)
                                  [(list 'done ext) (format "~a" ext)]
                                  [_ ""])]
                               [enabled #f]
                               [stretchable-width #f]))
                 (goal-type (new message%
                                 [parent goal-panel]
                                 [label (format " : ~a" goal)]))
                 (refinement (new horizontal-panel%
                                  [parent this]
                                  [alignment '(left top)]
                                  [stretchable-height #f])))

            (new text-field%
                 [parent refinement]
                 [label "by"]
                 [init-value (get-field tactic-text proof-step)]
                 [enabled (member (car (get-field status proof-step))
                                  '(incomplete error))]
                 [callback (lambda (field event)
                             (set-field! tactic-text proof-step
                                         (send field get-value))
                             (when (equal? (send event get-event-type)
                                           'text-field-enter)
                               (refine proof-step)))])
            (new button%
                 [parent refinement]
                 [label "Refine"]
                 [callback (lambda (x y)
                             (when proof-step
                               (refine proof-step)))]))))

    (define/public (notify-change step)
      (update-step-display))))

(define/contract (goal->string proof-goal)
  (-> (is-a?/c proof-step%) string?)
  (format "~a ⊢ ~a : ~a"
          (let ((Γ (reverse (get-field context proof-goal))))
            (if (null? Γ)
                "·"
                (string-join (for/list ([elt Γ])
                               (format "~a:~a" (car elt) (cadr elt)))
                             ", ")))
          (match (get-field status proof-goal)
            [(list 'incomplete) "?"]
            [(list 'refined _) "➘"]
            [(list 'error _) "✘"]
            [(list 'done ext) ext])
          (get-field goal proof-goal)))

(define/contract (goal-to-hierarchical-list goal h-list)
  (-> (is-a?/c proof-step%)
      (or/c (is-a?/c hierarchical-list%)
            (is-a?/c hierarchical-list-compound-item<%>))
      void?)

  (define step-observer-mixin
    (mixin (hierarchical-list-item<%>)
        (proof-step-observer<%>)
      (define/public (notify-change step)
        (let ((editor (send this get-editor)))
          (send editor select-all)
          (send editor clear)
          (send editor insert (goal->string step)))
        (when (is-a? this hierarchical-list-compound-item<%>)
          (for ([i (send this get-items)])
            (send this delete-item i)))
        (for ([subgoal (get-field subgoals step)])
          (goal-to-hierarchical-list subgoal this)))
      (super-new)))

  (let* ((subgoals (get-field subgoals goal))
         (new-item (if (null? subgoals)
                       (send h-list new-list step-observer-mixin)
                       (send h-list new-list step-observer-mixin)))
         (item-editor (send new-item get-editor)))
    (send new-item user-data goal)
    (send goal add-observer new-item)
    (send item-editor insert (goal->string goal))
    (for ([subgoal subgoals])
      (goal-to-hierarchical-list subgoal new-item))))

(define hierarchical-proof-step-list%
  (class hierarchical-list%
    (init-field parent
                [style '(no-hscroll)]
                [select-callback (lambda (i) (void))])
    (super-new [parent parent] [style style])
    (define/override (on-select i)
      (super on-select i)
      (select-callback i))))

;;;; Controllers

(define/contract (refine proof-step)
  (-> unrefined-proof-step? void?)
  (with-handlers ([exn:fail? (lambda (exn)
                               (displayln (exn->string exn))
                               (set-field! status proof-step
                                           (list 'error exn)))])
    (let* ((parsed (read (open-input-string (get-field tactic-text proof-step))))
           (refinement ((eval-rule parsed)
                        (send proof-step get-sequent)))
           (subgoals (refinement-new-goals refinement))
           (extractor (refinement-extract refinement)))
      (if (null? subgoals)
          (set-field! status proof-step (list 'done (extractor empty)))
          (set-field! status proof-step (list 'refined extractor)))
      (set-field! subgoals proof-step
                  (for/list ([g subgoals])
                    (sequent->proof-step g #:parent proof-step)))
      (send proof-step update-observers)
      (send proof-step update-parent-status))))

;;;; The app

(define proof-editor-frame%
  (class frame%
    (init sequent
          [width 700]
          [height 700])
    (super-new [label "Proof editor"])

    (define panel (new vertical-panel% [parent this]))

    (define step-list
      (new hierarchical-proof-step-list%
           [parent panel]
           [select-callback
            (lambda (i)
              (when i
                (send details set-proof-step
                      (send i user-data))))]))
    (send step-list allow-deselect #t)
    (goal-to-hierarchical-list (sequent->proof-step sequent) step-list)

    (define details
      (new proof-goal-editor-panel% [parent panel]))
    (send details set-proof-step #f)))


(define/contract (prove sequent)
  (-> sequent? void?)
  (define frame (new proof-editor-frame% [sequent sequent]))
  (send frame show #t)
  (void))
