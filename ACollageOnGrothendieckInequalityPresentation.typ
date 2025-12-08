#import "@preview/touying:0.6.1": *
#import "@preview/datify:1.0.0"
#import "themes/university.typ": *
#import "@preview/theorion:0.4.1": *
#import cosmos.clouds: *


#let date = datetime(day: 10, month: 12, year: 2025)

#show: show-theorion

#show: university-theme.with(
  aspect-ratio: "16-9",
  config-info(
    title: [Un collage sobre la desigualdad de Grothendieck],
    subtitle: [Seminario de titulación I],
    author: [Antonio Barragán Romero \ Maite Fernández Unzueta],
    date: datify.custom-date-format(date, lang: "es"),
    logo: emoji.leaf.herb,
  ),
  header-right: self => box(utils.display-current-heading(level: 1)) + h(.3em) + self.info.logo,
  config-common(frozen-counters: (theorem-counter)),
)

#set par(justify: true)
#let theorem = theorem.with(fill: rgb("#1b7491aa"))

#title-slide(
  authors: (
    [
      Antonio Barragán Romero. \
      #link("mailto:antonio.barragan@cimat.mx")
    ],
    [
      Maite Fernández Unzueta. \
      #link("mailto:maite@cimat.mx")
    ],
  ),
  logo: none,
)

= Introducción

= Desigualdad de Khintchine

==
#definition[

]
#theorem(title: "Desigualdad de Khintchine")[

]
#proposition[]

= Desigualdad de Grothendieck

==
#theorem(title: "Desigualdad de Grothendieck")[

]
= Usos y aplicaciones


#bibliography("biblio.yml")

#slide()[
  #set text(size: 16pt)
  // #bibliography("biblio.yml", full: true)
]
