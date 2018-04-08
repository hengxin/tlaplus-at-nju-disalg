#!/bin/bash

## The extracted hyperbook has broken permissions
chmod 664 *.tex

## Create the top level combined.tex file which is eventually used
## to generate the single pdf
cat > combined-gen.tex << EOF
\documentclass[english,fleqn,leqno]{article}
\usepackage[T1]{fontenc}
\usepackage[latin9]{inputenc}

\makeatletter
\usepackage{standalone}
\usepackage{hypertlabook}
\usepackage{graphpap}
\usepackage{hyperref}
\usepackage{babel}

\makeatother
\makeindex

%% Overwrite tindex and ctindex for the moment because they don't work in a single
%% big document. Haven't figured out why.
\renewcommand{\tindex}[2]{\index{#2}}
\renewcommand{\ctindex}[2]{\index{#2}}
\renewcommand{\ctindex}[3]{\index{#2}}

%% Rewrite refs to standalone pdf
\renewcommand{\popref}[2]{\hyperref[#1]{#2}}
\renewcommand{\target}[1]{\label{#1}}
\renewcommand{\btarget}[1]{\label{#1}}
\renewcommand{\rref}[3]{\hyperref[#2]{#3}}
\renewcommand{\sref}[3]{\hyperref[#2]{#3}}

%% Get rid of navigation buttons at the left. In a single document pdf, navigation
%% is provided by the viewer.
\renewcommand{\helpbutton}{}
\renewcommand{\backbutton}{}
\renewcommand{\fwdbutton}{}
\renewcommand{\tlabutton}{}
\renewcommand{\contentsbutton}{}
\renewcommand{\indexbutton}{}
\renewcommand{\summarybutton}{}

%%%% main.tex preamble
% PROOF
\beforePfSpace{0pt}
\afterPfSpace{0pt}
\interStepSpace{0pt}

% State commands

% DieHard: [big = #1, small = #2]
\newcommand{\dhstate}[2]{\left[\!\begin{array}{l@{\,\,}c@{\,\,}c}
                        big & = & #1 \\\\ small & = & #2
                        \end{array}\!\right]}

%Euclid: [x = #1, y = #2, pc = #3]
\newcommand{\pestate}[3]{\left[\!\begin{array}{l@{\,\,}c@{\,\,}c}
                        x & = & #1 \\\\ y & = & #2 \\\\ pc & = & #3
                        \end{array}\!\right]}

%Alternation: [b = #1, box = #2]
\newcommand{\altstate}[2]{\left[\!\begin{array}{l@{\,\,}c@{\,\,}c}
                        b & = & #1 \\\\ box & = & #2
                        \end{array}\!\right]}

% Handshake : [p = #1, c = #2, box = #3, bBar = #4, boxBar = #3]
\newcommand{\hdskstate}[4]{\left[\!\begin{array}{l@{\,\,}c@{\,\,}c}
                        p & = & #1 \\\\ c & = & #2 \\\\ box & = & #3 \\\\
                        \ov{b} & = & #4 \\\\ \ov{box} & = & #3
                        \end{array}\!\right]}

% 2-step Handshake : [p = #1, c = #2, box = #3, pc = 0 :> #4 @@ 1 :> #5]
\newcommand{\hdskkstate}[5]{\left[\!\begin{array}{l@{\,\,}c@{\,\,}l}
                        p & = & #1 \\\\ c & = & #2 \\\\ box & = & #3 \\\\
                        pc & = & 0 :> #4\,@\!@ \\\\ & & 1:>#5 
                        \end{array}\!\right]}
%%%% end main.tex


%%%%% proof.tex preamble
\newcommand{\G}{\textbf{G}}
\newcommand{\Sym}{\ensuremath{\mathcal{S}}}
\newcommand{\FK}{\ensuremath{\mathcal{F}_{K}}}
\newcommand{\FU}{\ensuremath{\mathcal{F}_{U}}}
\newcommand{\DK}{\ensuremath{\mathcal{D}_{K}}}
\newcommand{\DU}{\ensuremath{\mathcal{D}_{U}}}
\newcommand{\BB}{\ensuremath{\mathcal{B}}}
%%%% end proof.tex

%%%% summary.tex preamble
\newcommand{\notemark}[1]{$^{\mbox{\tiny(#1)}}$}
\newcommand{\atat}{\mathop{@@}}
%%%% end summary.tex

%%%% condorcet[2,3]-proof.tex
\newcommand{\cset}{\ensuremath{\mathcal{CW}}} %duplicated in specification.tex
\pflongnumbers
\pflongindent
\beforePfSpace{10pt, 5pt, 2pt}
\afterPfSpace{10pt, 5pt, 2pt}
\interStepSpace{10pt, 5pt, 2pt}
%%%% end condorcet2-proof.tex

%%%% euclid-proof-5-ascii.tex
% manually removed \listfiles from the first line of the file
%%%% end euclid-proof-5-ascii.tex

%%%% w2f-proof.tex
\newcommand{\NC}{\ensuremath{\langle\N\land C\rangle_{v}}}
\newcommand{\B}{\ensuremath{\langle\ov{B}\rangle_{\ov{w}}}}
\newcommand{\NA}{\ensuremath{\langle\N\land A\rangle_{v}}}
%\newcommand{\EB}{\ensuremath{\ov{\ENABLED\langle{B}\rangle_{{w}}}}}
\newcommand{\EB}{\ensuremath{EB}}
\newcommand{\EA}{\ensuremath{\ENABLED\langle{A}\rangle_{{v}}}}
\newcommand{\SNC}{\ensuremath{[\N\land\neg C]_{v}}}
%%%% end w2f-proof.tex

%%%% bbuf-r2.tex
\newcommand{\chpr}{chBar'} % prime for
%%%% end bbuf-r2.tex

\begin{document}

%% start.tex title
\vspace*{10pt}
\begin{center}
\hspace*{50pt}{\LARGE\boldmath\textbf{\makebox[0pt]{Principles and Specifications of Concurrent Systems}}}\V{.5}
{\large \hspace*{50pt}\s{1}Leslie Lamport \V{.3}
\hspace*{50pt}Version of \dayMonthYear}
\end{center}

\tableofcontents

\newpage
\renewcommand{\contentsname}{The \emph{Principles} and \emph{Specification} 
       Tracks\protect\target{top}}
\input{main.tex}

\newpage
\renewcommand{\contentsname}{The \emph{Principles} Track\protect\target{top}}
\addtocounter{section}{1}
\input{principles.tex}

\newpage
\renewcommand{\contentsname}{The \emph{Specification} Track\protect\target{top}}
\addtocounter{section}{1}
\input{specification.tex}

\newpage
\renewcommand{\contentsname}{The \protect\tlaplus\ Proof Track\protect\target{top}}
\input{proof.tex}

\newpage
\renewcommand{\contentsname}{Math\protect\target{top}}
\addtocounter{section}{1}
\input{math.tex}

\input{topics.toc}

\newpage
\renewcommand{\contentsname}{Summary of \protect\tlaplus\protect\target{top}}
\input{summary.tex}

%%%% Auxiliary pages referenced from within the main content above
%%%% Include all auxiliary tex files
\newpage
\input{combined-aux.tex}

%%% Index does not work yet
%\newpage
%\addcontentsline{toc}{chapter}{Index}
%\printindex

\end{document}
EOF

## These files are directly referenced by combined.tex
PROCESSED="main.tex principles.tex specification.tex math.tex proof.tex summary.tex "

## These files are temporarily generated. Don't create self-references.
PROCESSED+="combined.tex combined-gen.tex combined-aux.tex "

## These files don't make sense in a single pdf
PROCESSED+="BOOKMARK.tex topics.tex index.tex start.tex content.tex "

## These files - for one or another reason - cause problems (mostly due to their preamble).
## This list should be empty!!!
## E.g. some define newcommands with identical names which causes duplicate definitions => Move to hyperbooktla.sty.
## Others define newcommands with identical names but different "implementation" => Rename one of them.
## For others, parts of their preable have been extracted to combined-gen.tex
PROCESSED+="handshake-question.tex modular-arithmetic-fig-1.tex modular-arithmetic-fig-2.tex modular-arithmetic-fig-3.tex modular-arithmetic-fig-4.tex modular-arithmetic-fig-5.tex glossary.tex subexpressions.tex toolbox-impl.tex "
## A few in-place edits to fix problems. The changes seem innocent enough.
## * Remove \listfiles from euclid-proof-5-ascii.tex
sed -i 's/\\listfiles//' euclid-proof-5-ascii.tex
## * Remove definition of newcommand cset from specification.tex (conflicting 
##   declaration in condorcet-proof.tex in the preamble.
sed -i 's/\\newcommand{\\cset}{\\ensuremath{\\mathcal{CW}}}//' specification.tex

## Create the header of the combined-popups.tex file
echo "\begin{document}" > combined-aux.tex

mkdir -p popup/
## loop through all "popup" .tex files and replace the popup with
## document in the popup/ directory.
for f in `grep -l 'begin{popup}' *.tex` ; do
    if [[ $PROCESSED != *$f* ]]
    then
        # Replace begin{popup } with begin{document}
        awk '{ gsub("{popup}", "{document}") ; print $0 }' $f > popup/$f

        ## Add to combined-aux.tex
        echo "\newpage" >> combined-aux.tex
        echo "\input{popup/$f}" >> combined-aux.tex
        echo "\label{${f%.tex}}" >> combined-aux.tex
    fi

    # mark file as processed
    PROCESSED+="$f "
done

## loop over remaining files and append them to combined-aux.tex
for f in *.tex; do
    if [[ $PROCESSED != *$f* ]]
    then
        ## Add to combined-aux.tex
        echo "\newpage" >> combined-aux.tex
        echo "\input{$f}" >> combined-aux.tex
        echo "\label{${f%.tex}}" >> combined-aux.tex
    fi
done

echo "\end{document}" >> combined-aux.tex

pdflatex combined-gen.tex
pdflatex combined-gen.tex

## Final cleanup
rm -rf popup/
rm combined-gen.tex
rm combined-aux.tex

mv combined-gen.pdf HyperBook.pdf
echo "=================================="
echo "Done creating single HyperBook.pdf"
echo "=================================="
