#lang racket
(require racket/class)
(require racket/gui/base)
(require "tt.rkt")

(define proof-goal-panel%
  (class object%
    (init goal parent)
    (field (extractor #f))

    (super-new)

    (define outer-panel (new vertical-panel%
                             [parent parent]
                             [alignment '(left top)]))
    (define inner-panel (new horizontal-panel%
                             [parent outer-panel]
                             [alignment '(left top)]))
    (define goal-view (new message% [parent inner-panel]
                           [label (format "~a" goal)]))
    (define tactic-entry (new text-field% [parent inner-panel]
                              [label "Rule"]))

    (define (refine button event)
      (let* ((input (send tactic-entry get-value))
             (parsed (read (open-input-string input)))
             (refine (eval `(,parsed ,goal)))
             (subgoals (refinement-new-goals refine))
             (extract (refinement-extract refine)))
          (set-field! extractor this extract)
          (new proof-step-panel%
               [parent outer-panel]
               [subgoals subgoals])))
    (define button (new button% [parent inner-panel]
                        [label "Refine"]
                        [callback refine]))))

(define proof-step-panel%
  (class object%
    (init subgoals parent)
    (super-new)
    (define outer-panel (new horizontal-panel%
                             [parent parent]
                             [alignment '(left top)]))
    (define spacer (new pane% [parent outer-panel] [min-width 30]))
    (define inner-panel (new vertical-panel%
                             [parent outer-panel]
                             [alignment '(left top)]))
    (for ([goal subgoals])
      (new proof-goal-panel% [parent inner-panel] [goal goal]))))


(define (prove thm)
  (define goals (list thm))

  (define frame (new frame%
                     [label "TT Interactions"]
                     [width 800]
                     [height 600]))

  (define mb (new menu-bar% [parent frame]))
  (define m-edit (new menu% [label "Edit"] [parent mb]))
  (append-editor-operation-menu-items m-edit #f)

  (define initial-goal (new proof-goal-panel% [parent frame] [goal thm]))
  (send frame show #t))
