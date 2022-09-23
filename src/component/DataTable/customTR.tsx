import PropTypes from "prop-types";
import React from "react";

interface CustomTRProps {
    item: any;
    columns: Array<any>;
}

export function CustomTR({item, columns}:CustomTRProps) {
    const customTD = columns.map((column, index) => {
        return <td key={index} className="p-3 border border-neutral-800 border-collapse text-center">{item[column.key]}</td>
    });

    return (
        <tr className="odd:bg-neutral-600 even:bg-neutral-700">
            {customTD}
        </tr>
    );
}

CustomTR.propTypes = {
    item: PropTypes.any.isRequired,
    columns: PropTypes.array.isRequired,
}
