import React from "react";
import "./react-data-table.css";

export interface ReactDataTableProps {
    label: string;
}
  
const ReactDataTable = ({label}: ReactDataTableProps) => {
    return <button>{label}</button>;
};
  
export default ReactDataTable;
