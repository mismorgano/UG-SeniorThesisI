import os
from pathlib import Path
import argparse


def read_template(path: Path) -> str:
    return Path(path).read_text(encoding="utf-8")


def make_pdf_list(pdf_path: Path, item_template: str):
    pdf_files = [f for f in os.listdir(pdf_path) if f.endswith(".pdf")]
    pdf_files.sort()
    links = "\n".join(
        item_template.format(pdf=pdf, id=id) for id, pdf in enumerate(pdf_files)
    )
    return links


def generate_index(template: str, links: list[str], out_dir: Path):
    index = Path(os.path.join(out_dir, "index.html"))
    index.parent.mkdir(parents=True, exist_ok=True)
    index.write_text(template.format(links=links), encoding="utf-8")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("dir", help="the path to the PDFs", type=Path)

    args = parser.parse_args()
    pdfdir = args.dir

    html_template = read_template("template.html")
    pdf_item = read_template("pdf_item.html")
    pdf_links = make_pdf_list(pdfdir, pdf_item)

    generate_index(html_template, pdf_links, pdfdir)


if __name__ == "__main__":
    main()
