// Returns a function responsible for sorting a specific column index 
// (key = columnKey, asc = ascending order?).
export const Comparer = (key: string, asc: boolean) => {
    // This is used by the array.sort() function...
    return function(item1: any, item2: any) {

        // This is a transient function, that is called straight away. 
        // It allows passing in different order of args, based on 
        // the ascending/descending order.
        return function(value1, value2) {

            // sort based on a numeric or localeCompare, based on type...
            return (value1 !== "" && value2 !== "" && !isNaN(value1) && !isNaN(value2))
                ? value1 - value2
                : value1.toString().localeCompare(value2);
        }(asc ? item1[key] : item2[key], asc ? item2[key] : item1[key]);
    }
};
