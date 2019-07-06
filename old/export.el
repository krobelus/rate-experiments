(package-initialize)
(require 'ox-pandoc)
(require 'org-ref)

(setq make-backup-files nil)

(setq org-confirm-babel-evaluate nil)
(org-babel-do-load-languages 'org-babel-load-languages '((shell . t)))

(setq org-latex-pdf-process (list "latexmk -shell-escape -bibtex -f -pdf %f"))
(setq org-latex-listings 'minted
      org-latex-packages-alist '(("" "minted")))

;(org-pandoc-export-to-markdown)
;(org-html-export-to-html)
;(org-latex-export-to-pdf)

; export commands are async for some reason
(defun sleep () (sleep-for 1))
