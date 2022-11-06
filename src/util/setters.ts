import { Dispatch, SetStateAction } from "react";

export type Setter<T> = Dispatch<SetStateAction<T>>;

export const applyAction = <T>(action: SetStateAction<T>, prev: T): T => action instanceof Function ? action(prev) : action;
