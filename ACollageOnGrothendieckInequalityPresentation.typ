#import "@preview/touying:0.6.1": *
#import "@preview/datify:1.0.0"
#import "themes/university.typ": *

#let date = datetime(day: 10, month: 12, year: 2025)

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
)
#set par(justify: true)

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

= First slide

== Second Slide

#lorem(100)

== Third slide

#lorem(100)

#slide()[
  #set text(size: 16pt)
  #bibliography("biblio.yml", full: true)
]

// #set rect(
//   width: 100%,
//   height: 100%,
//   inset: 4pt,
// )

// #set page(
//   paper: "iso-b7",
//   header: rect(fill: aqua)[Header],
//   footer: pad(x: -1em,rect(fill: aqua)[Footer]),
//   number-align: center,
//   footer-descent: 1pt
// )

// #rect(fill: aqua.lighten(40%))
