(package-initialize)
(setq package-archives
    '(("gnu" . "http://elpa.gnu.org/packages/")
      ("melpa" . "http://melpa.milkbox.net/packages/")))
(package-refresh-contents)
(package-install 'ox-pandoc)
(package-install 'org-ref)
