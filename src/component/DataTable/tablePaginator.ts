// Constants
const PAGE_LIMIT = 4;

// Returns an array of page indexes to display with buttons or spans 
// calculated from the currentPage index and the pageCount (max number of pages)
export const Paginator = (currentPage: number, pageCount: number) => {
    let pages = [];
    
    // If there is 6 or less pages, we show each of them
    if (pageCount <= 7) {
        for (let i = 1; i <= pageCount; i++) {
            pages.push(i);
        }

        return pages;
    }

    /* ---- There is more than 7 pages, calculating the correct display ---- */
    
    // If the current page is at the start (1 -> 4), we show pages 1 -> 5 and <last page number>
    if (currentPage <= PAGE_LIMIT) {
        for (let i = 1; i <= (PAGE_LIMIT + 1); i++) {
            pages.push(i);
        }

        pages.push(-1);
        pages.push(pageCount);

        return pages;
    }

    // If the current is at the end we show the pages calculated from <pageCount - PAGE_LIMIT> to <pageCount>
    if ((pageCount - currentPage) < PAGE_LIMIT) {
        for (let i = pageCount; i >= (pageCount - PAGE_LIMIT); i--) {
            pages.push(i);
        }

        pages.push(-1);
        pages.push(1);

        return pages.reverse();
    }

    return [1, -1, currentPage - 1, currentPage, currentPage + 1, -1, pageCount];
}
