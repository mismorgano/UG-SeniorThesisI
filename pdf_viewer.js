
pdfjsLib.GlobalWorkerOptions.workerSrc = 'https://cdnjs.cloudflare.com/ajax/libs/pdf.js/5.0.375/pdf.worker.min.mjs'

function getURL(aElement) {
    let url = new URL(aElement.href);
    return url.pathname;
}

function loadPDF(canvasID, url) {
    let loadingTask = pdfjsLib.getDocument(url);

    loadingTask.promise.then(pdf => {
        console.log('PDF loaded');

        let pageNumber = 1;
        pdf.getPage(pageNumber).then(page => {
            console.log('Page loaded');

            let scale = 1;
            let viewport = page.getViewport({ scale: scale });

            let canvas = document.getElementById(canvasID);

            let context = canvas.getContext('2d');


            canvas.width = viewport.width * window.devicePixelRatio;
            canvas.height = viewport.height * window.devicePixelRatio;
            canvas.style.width = viewport.width + "px";
            canvas.style.height = viewport.height + "px";

            context.scale(window.devicePixelRatio, window.devicePixelRatio);
            let renderContext = {
                canvasContext: context,
                viewport: viewport,
                intent: 'display'
            };

            let renderTask = page.render(renderContext);
            renderTask.promise.then(() => {
                console.log('Page rendered');
            })
        })
    })
}

let pdfs = document.getElementsByTagName("a");

for (let pdf of pdfs) {

    const url = getURL(pdf);
    const canvasID = pdf.firstElementChild.id;

    loadPDF(canvasID, url);
}