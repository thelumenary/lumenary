/**
 * Preferences stored in the browser and applied by an inline script before first paint, so the
 * page never flashes the wrong state. Kept outside the "use client" toggles so that the server
 * layout imports plain strings.
 */
export const THEME_KEY = "lumenary:theme";
export const CATS_KEY = "lumenary:cats";

export const initScript =
  `try{var t=localStorage.getItem("${THEME_KEY}");if(t==="light"||t==="dark")document.documentElement.setAttribute("data-theme",t)}catch(e){}` +
  `try{if(localStorage.getItem("${CATS_KEY}")==="hidden")document.documentElement.setAttribute("data-cats","hidden")}catch(e){}`;
