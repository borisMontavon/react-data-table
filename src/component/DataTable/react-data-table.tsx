import React from "react";
import PropTypes from "prop-types";
import { useEffect, useState } from "react";

import { FontAwesomeIcon } from "@fortawesome/react-fontawesome";
import { faArrowUpLong, faArrowDownLong, faArrowsUpDown } from "@fortawesome/free-solid-svg-icons";

import { CustomTR } from "./customTR";
import { Comparer } from "./tableComparer";
import { Paginator } from "./tablePaginator";

interface ReactDataTableProps {
    data: {"data": Array<any>, "columns": Array<any>};
}

// Custom datatable handling plugin with react
export default function ReactDataTable({data}:ReactDataTableProps) {
    const [sortedData, setSortedData] = useState<Array<any>>([]);
    const [columns, setColumns] = useState<Array<any>>([]);
    const [maxRows, setMaxRows] = useState(10);
    const [isSearched, setIsSearched] = useState(false);
    const [currentPage, setCurrentPage] = useState(1);

    // Initializing the data and columns for the table 
    useEffect(() => {
        // Creating the data
        const initData = data.data.map((item) => {
            return {
                ...item,
                "show": true
            };
        });

        setSortedData(initData);

        // Creating the columns
        const initColumns = data.columns.map((column) => {
            return {
                ...column,
                "sortBy": "none",
                "arrowIcon": faArrowsUpDown
            };
        });

        setColumns(initColumns);
    }, [data]);

    // Sorting table data by value of column clicked
    // @param e: event of the click
    // @param column: column clicked
    const sortByColumn = (e: React.MouseEvent<HTMLTableHeaderCellElement, MouseEvent>, column: any) => {
        e.preventDefault();
        e.stopPropagation();

        // Switching icons and sorting method for the column clicked
        switch (column.sortBy) {
            case "asc":
                column.sortBy = "desc";
                column.arrowIcon = faArrowDownLong;
                break;
            case "desc":
            default:
                column.sortBy = "asc";
                column.arrowIcon = faArrowUpLong;
                break;
        }

        // Reseting the other columns
        columns.forEach((item: any) => {
            if (item.key !== column.key) {
                item.sortBy = "none";
                item.arrowIcon = faArrowsUpDown;
            }
        });

        const newlySortedData = [...sortedData];
        
        // Sorting the data by result to the Comparer function call
        newlySortedData.sort(Comparer(column.key, column.sortBy === "asc"));
        
        setSortedData(newlySortedData);
        setCurrentPage(1);
    };

    // Filtering the data by search string
    // @param e: event of the input containing the search string
    const handleSearch = (e: React.ChangeEvent<HTMLInputElement>) => {
        const searchString = e.target.value;

        // If no input string is specified, we show everything
        // If an input string is specified, we filter by inclusion
        if (searchString === "") {
            sortedData.forEach((item: any) => {
                item.show = true;
            });
            setIsSearched(false);
        } else {
            sortedData.forEach((item: any) => {
                item.show = columns.some((column: any) => item[column.key].toLowerCase().includes(searchString.toLowerCase()));
            });
            setIsSearched(true);
        }

        const newlySortedData = [...sortedData];

        setSortedData(newlySortedData);
        setCurrentPage(1);
    };

    // Setting the maximum number of rows to be displayed on one page
    // @param e: click event on the select element
    const handleEntries = (e: React.ChangeEvent<HTMLSelectElement>) => {
        setMaxRows(Number(e.target.value));
        setCurrentPage(1);
    };

    // Calculating the number of entries (rows) to be displayed (show === true)
    const nbEntries = sortedData.filter((item: any) => item.show).length;

    // Rendering the header cells
    const customTH = columns.map((item: any, index: number) => {
        return <th key={index} className="p-3 border border-neutral-800 border-collapse cursor-pointer" onClick={(e) => sortByColumn(e, item)}>
            {item.title}
            <FontAwesomeIcon icon={item.arrowIcon} className="text-neutral-500 ml-2" />
        </th>;
    });

    // Calculating the number of pages (number of rows to display / total number of rows)
    const pageCount = Math.ceil(nbEntries / maxRows);

    // Handling the click on the Previous button
    const handlePreviousPage = () => {
        if (currentPage > 1) {
            setCurrentPage(currentPage - 1);
        }
    };

    // Handling the click on the Next button
    const handleNextPage = () => {
        if (currentPage < pageCount) {
            setCurrentPage(currentPage + 1);
        }
    };

    // Handling the click on a generic page button
    // @param value: the index of the page
    const handleGoToPage = (value: number) => {
        setCurrentPage(value);
    };

    let pageButtons: any[] = [];
    let previousButtonDisabled, nextButtonDisabled;

    // Rendering the pages buttons
    if (pageCount > 0) {
        // Getting the pages to display
        const pages = Paginator(currentPage, pageCount);

        // If there is at least one page to show, the disabled attribute of the Previous and Next button is calculated from the current page index
        previousButtonDisabled = currentPage === 1;
        nextButtonDisabled = currentPage === pageCount;

        pageButtons = pages.map((item, index) => {
            if (item === currentPage) {
                return <button
                            className="bg-teal-700 py-1 px-2 ml-2 rounded-md text-white border border-teal-700"
                            key={index}
                        >
                            {item}
                        </button>
            }

            if (item > 0) {
                return <button
                        className="bg-transparent py-1 px-2 ml-2 rounded-md text-white border border-white transition-all hover:bg-white hover:text-black"
                        key={index}
                        onClick={() => handleGoToPage(item)}
                    >
                        {item}
                    </button>
            }

            return <span 
                className="bg-transparent ml-2 text-white"
                key={index}
            >
                ...
            </span>
        });
    } else {
        // There is no page to show (= no rows to show), so the Previous and Next button are automatically disabled
        previousButtonDisabled = true;
        nextButtonDisabled = true;
    }

    let nbRows = 0;

    // Rendering the rows according to the max rows to show on a page and the current page index
    const rows = sortedData.map((item: any, index: number) => {
        if (item.show && nbRows < maxRows && index + 1 > ((currentPage - 1) * maxRows)) {
            nbRows++;

            return <CustomTR key={index} item={item} columns={data.columns} />;
        }

        return null;
    });

    let startRowCount, endRowCount;

    if (currentPage === 1) {
        startRowCount = 1;
    } else {
        startRowCount = (currentPage - 1) * maxRows;
    }

    if (currentPage === pageCount) {
        endRowCount = nbEntries;
    } else {
        endRowCount = nbRows * currentPage;
    }

    // Rendering the current pagination state (according to search state as well)
    const entriesSummary = isSearched ?
    <span className="text-white">Showing {startRowCount} to {endRowCount} of {nbEntries} entries (filtered from {sortedData.length} total entries)</span> :
    <span className="text-white">Showing {startRowCount} to {endRowCount} of {nbEntries} entries</span>;

    return (
        <div>
            <div className="flex justify-between items-center mb-3">
                <div>
                    <span
                        className="text-white"
                    >
                        Show
                    </span>
                    <select
                        id="inputTableSearch"
                        className="mx-2 p-1 rounded outline-none outline-offset-1 focus-visible:outline-teal-700"
                        onChange={(e) => handleEntries(e)}
                    >
                        <option value={10}>10</option>
                        <option value={25}>25</option>
                        <option value={50}>50</option>
                        <option value={100}>100</option>
                    </select>
                    <span
                        className="text-white"
                    >
                        entries
                    </span>
                </div>
                <div>
                    <label
                        htmlFor="inputTableSearch"
                        className="text-white"
                    >
                        Search :
                    </label>
                    <input
                        id="inputTableSearch"
                        type="text"
                        className="ml-3 p-1 rounded outline-none outline-offset-1 focus-visible:outline-teal-700"
                        onChange={(e) => handleSearch(e)}
                    />
                </div>
            </div>
            <div>
                <table className="border border-neutral-800 text-white">
                    <thead>
                        <tr>
                            {customTH}
                        </tr>
                    </thead>
                    <tbody>
                        {rows}
                    </tbody>
                </table>
            </div>
            <div className="flex justify-between items-center mt-3">
                <div>
                    {entriesSummary}
                </div>
                <div className="flex justify-center items-center">
                    <button
                        id="prevButton"
                        className="bg-transparent py-1 px-2 rounded-md text-white border border-white transition-all hover:bg-white hover:text-black disabled:border-neutral-600 disabled:text-neutral-600 disabled:hover:bg-transparent"
                        disabled={previousButtonDisabled}
                        onClick={handlePreviousPage}
                    >
                        Previous
                    </button>
                    <div>
                        {pageButtons}
                    </div>
                    <button
                        id="nextButton"
                        className="bg-transparent py-1 px-2 ml-2 rounded-md text-white border border-white transition-all hover:bg-white hover:text-black disabled:border-neutral-600 disabled:text-neutral-600 disabled:hover:bg-transparent"
                        disabled={nextButtonDisabled}
                        onClick={handleNextPage}
                    >
                        Next
                    </button>
                </div>
            </div>
        </div>
    );
}

ReactDataTable.propTypes = {
    data: PropTypes.object.isRequired
}
