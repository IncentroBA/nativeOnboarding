/**
 * @typedef Property
 * @type {object}
 * @property {string} key
 * @property {string} caption
 * @property {string} description
 * @property {string[]} objectHeaders
 * @property {ObjectProperties[]} objects
 * @property {Properties[]} properties
 */

/**
 * @typedef ObjectProperties
 * @type {object}
 * @property {PropertyGroup[]} properties
 * @property {string[]} captions
 */

/**
 * @typedef PropertyGroup
 * @type {object}
 * @property {string} caption
 * @property {PropertyGroup[]} propertyGroups
 * @property {Property[]} properties
 */

/**
 * @typedef Properties
 * @type {PropertyGroup}
 */

/**
 * @typedef Problem
 * @type {object}
 * @property {string} property
 * @property {("error" | "warning" | "deprecation")} severity
 * @property {string} message
 * @property {string} studioMessage
 * @property {string} url
 * @property {string} studioUrl
 */

/**
 * @param {object} values
 * @param {Properties} defaultProperties
 * @param {("web"|"desktop")} target
 * @returns {Properties}
 */
export function getProperties(values, defaultProperties, target) {
    // Do the values manipulation here to control the visibility of properties in Studio and Studio Pro conditionally.
    /* Example
    if (values.myProperty === "custom") {
        delete defaultProperties.properties.myOtherProperty;
    }
    */
    return defaultProperties;
}

// /**
//  * @param {Object} values
//  * @returns {Problem[]} returns a list of problems.
//  */
// export function check(values) {
//    /** @type {Problem[]} */
//    const errors = [];
//    // Add errors to the above array to throw errors in Studio and Studio Pro.
//    /* Example
//    if (values.myProperty !== "custom") {
//        errors.push({
//            property: `myProperty`,
//            message: `The value of 'myProperty' is different of 'custom'.`,
//            url: "https://github.com/myrepo/mywidget"
//        });
//    }
//    */
//    return errors;
// }

// /**
//  * @param {object} values
//  * @param {boolean} isDarkMode
//  * @returns {object}
//  */
// export function getPreview(values, isDarkMode) {
//     // Customize your pluggable widget appearance for Studio Pro.
//     return {
//         type: "Container",
//         children: []
//     };
// }
export function getPreview() {
    return {
        type: "Image",
        document: decodeURIComponent(
            "%3C%3Fxml version='1.0' encoding='UTF-8'%3F%3E%3Csvg xmlns='http://www.w3.org/2000/svg' width='120' height='250' viewBox='0 0 120 250'%3E%3Crect x='.66' width='118.68' height='250' rx='27.21' ry='27.21' fill='%23292929'/%3E%3Crect x='4.39' y='3.11' width='111.23' height='243.06' rx='22.96' ry='22.96' fill='%23eee'/%3E%3Cpath d='M30.99,.72l.5,4.81c.33,3.15,3.33,5.56,6.94,5.56h43.15c3.6,0,6.61-2.41,6.94-5.56l.5-4.81H30.99Z' fill='%23292929'/%3E%3Cpath d='M92.22,228.29v-5.7h.8l1.83,2.89c.42,.67,.75,1.27,1.02,1.85h.02c-.07-.77-.08-1.46-.08-2.35v-2.39h.69v5.7h-.74l-1.81-2.89c-.4-.63-.78-1.29-1.07-1.9h-.03c.04,.73,.06,1.41,.06,2.36v2.44h-.69Z'/%3E%3Cpath d='M98.18,226.38c.02,1.01,.66,1.42,1.4,1.42,.53,0,.85-.09,1.13-.21l.13,.53c-.26,.12-.71,.25-1.36,.25-1.26,0-2.01-.83-2.01-2.07s.73-2.21,1.92-2.21c1.34,0,1.69,1.18,1.69,1.93,0,.15-.02,.27-.03,.35h-2.88Zm2.18-.53c0-.47-.19-1.21-1.03-1.21-.75,0-1.08,.69-1.14,1.21h2.18Z'/%3E%3Cpath d='M102.33,224.2l.58,.88c.15,.23,.28,.44,.41,.67h.03c.14-.25,.27-.46,.41-.68l.58-.87h.8l-1.4,1.98,1.44,2.12h-.85l-.6-.92c-.16-.24-.3-.47-.44-.71h-.02c-.14,.25-.28,.47-.43,.71l-.59,.92h-.82l1.46-2.09-1.39-2.01h.83Z'/%3E%3Cpath d='M106.91,223.02v1.18h1.07v.57h-1.07v2.21c0,.51,.14,.8,.56,.8,.19,0,.34-.03,.43-.05l.03,.56c-.14,.06-.37,.1-.66,.1-.35,0-.63-.11-.8-.31-.21-.22-.29-.58-.29-1.07v-2.23h-.63v-.57h.63v-.98l.73-.19Z'/%3E%3Cpath d='M12.38,227.4c.33,.2,.81,.37,1.32,.37,.75,0,1.19-.4,1.19-.97,0-.53-.3-.84-1.07-1.13-.93-.33-1.51-.81-1.51-1.62,0-.89,.74-1.55,1.85-1.55,.58,0,1.01,.14,1.26,.28l-.2,.6c-.19-.1-.57-.27-1.08-.27-.78,0-1.07,.47-1.07,.85,0,.53,.35,.8,1.13,1.1,.97,.37,1.46,.84,1.46,1.68,0,.88-.65,1.64-2,1.64-.55,0-1.15-.16-1.46-.36l.19-.62Z'/%3E%3Cpath d='M17.36,226.08h.02c.1-.14,.25-.32,.36-.47l1.2-1.41h.9l-1.58,1.68,1.8,2.41h-.91l-1.41-1.96-.38,.42v1.54h-.74v-6.01h.74v3.79Z'/%3E%3Cpath d='M21.57,223.05c0,.25-.18,.46-.47,.46-.26,0-.45-.2-.45-.46s.19-.47,.47-.47,.46,.2,.46,.47Zm-.83,5.25v-4.1h.74v4.1h-.74Z'/%3E%3Cpath d='M22.72,225.53c0-.52-.02-.95-.03-1.34h.67l.03,.7h.02c.3-.5,.79-.8,1.46-.8,.99,0,1.74,.84,1.74,2.08,0,1.47-.9,2.2-1.86,2.2-.54,0-1.02-.24-1.26-.64h-.02v2.23h-.74v-4.44Zm.74,1.09c0,.11,.02,.21,.03,.3,.14,.52,.58,.87,1.12,.87,.79,0,1.24-.64,1.24-1.58,0-.82-.43-1.52-1.22-1.52-.51,0-.98,.36-1.13,.92-.03,.09-.05,.2-.05,.3v.7Z'/%3E%3Ccircle cx='51.16' cy='225.81' r='2.82' fill='%2348b0f7'/%3E%3Cpath d='M59.63,223.69c1.17,0,2.12,.95,2.12,2.12s-.95,2.12-2.12,2.12-2.12-.95-2.12-2.12,.95-2.12,2.12-2.12m0-.71c-1.56,0-2.82,1.26-2.82,2.82s1.26,2.82,2.82,2.82,2.82-1.26,2.82-2.82-1.26-2.82-2.82-2.82h0Z'/%3E%3Cpath d='M68.1,223.69c1.17,0,2.12,.95,2.12,2.12s-.95,2.12-2.12,2.12-2.12-.95-2.12-2.12,.95-2.12,2.12-2.12m0-.71c-1.56,0-2.82,1.26-2.82,2.82s1.26,2.82,2.82,2.82,2.82-1.26,2.82-2.82-1.26-2.82-2.82-2.82h0Z'/%3E%3Cpath d='M44.04,164.74c0,1.96-1.19,3-2.65,3s-2.56-1.17-2.56-2.89c0-1.81,1.13-3,2.65-3s2.56,1.19,2.56,2.89Zm-4.43,.09c0,1.22,.66,2.31,1.82,2.31s1.83-1.08,1.83-2.37c0-1.13-.59-2.32-1.82-2.32s-1.83,1.13-1.83,2.38Z'/%3E%3Cpath d='M44.97,164.66c0-.42,0-.77-.03-1.11h.66l.04,.68h.02c.2-.39,.68-.77,1.35-.77,.57,0,1.45,.34,1.45,1.74v2.45h-.74v-2.36c0-.66-.25-1.21-.95-1.21-.49,0-.87,.35-1,.76-.03,.09-.05,.22-.05,.35v2.46h-.74v-2.99Z'/%3E%3Cpath d='M49.64,167.65c.02-.28,.03-.69,.03-1.06v-4.95h.74v2.57h.02c.26-.46,.74-.75,1.4-.75,1.02,0,1.73,.85,1.73,2.09,0,1.46-.92,2.19-1.84,2.19-.59,0-1.07-.23-1.37-.77h-.03l-.03,.68h-.64Zm.77-1.64c0,.09,.02,.19,.03,.27,.14,.52,.58,.87,1.12,.87,.78,0,1.24-.63,1.24-1.57,0-.82-.42-1.52-1.22-1.52-.51,0-.98,.35-1.13,.91-.02,.08-.04,.19-.04,.3v.74Z'/%3E%3Cpath d='M58.2,165.57c0,1.51-1.05,2.17-2.04,2.17-1.11,0-1.96-.81-1.96-2.11,0-1.37,.9-2.17,2.03-2.17s1.97,.85,1.97,2.11Zm-3.25,.04c0,.9,.52,1.57,1.24,1.57s1.24-.67,1.24-1.59c0-.69-.35-1.57-1.23-1.57s-1.26,.81-1.26,1.59Z'/%3E%3Cpath d='M61.41,167.65l-.06-.52h-.03c-.23,.32-.67,.61-1.25,.61-.83,0-1.25-.58-1.25-1.18,0-.99,.88-1.53,2.46-1.52v-.08c0-.34-.09-.95-.93-.95-.38,0-.78,.12-1.07,.3l-.17-.49c.34-.22,.83-.36,1.35-.36,1.25,0,1.56,.85,1.56,1.68v1.53c0,.36,.02,.7,.07,.98h-.68Zm-.11-2.09c-.81-.02-1.74,.13-1.74,.92,0,.48,.32,.71,.7,.71,.53,0,.87-.34,.99-.69,.03-.08,.04-.16,.04-.24v-.71Z'/%3E%3Cpath d='M63.22,164.83c0-.48,0-.9-.03-1.28h.65l.03,.8h.03c.19-.55,.63-.9,1.13-.9,.08,0,.14,0,.21,.03v.7c-.08-.02-.15-.03-.25-.03-.52,0-.9,.4-1,.96-.02,.1-.03,.22-.03,.35v2.18h-.74v-2.82Z'/%3E%3Cpath d='M69.44,161.64v4.95c0,.36,0,.78,.03,1.06h-.67l-.03-.71h-.02c-.23,.46-.73,.8-1.4,.8-.99,0-1.75-.84-1.75-2.08,0-1.36,.84-2.2,1.84-2.2,.63,0,1.05,.3,1.24,.63h.02v-2.45h.74Zm-.74,3.58c0-.09,0-.22-.03-.31-.11-.47-.52-.86-1.07-.86-.77,0-1.23,.68-1.23,1.58,0,.83,.41,1.51,1.21,1.51,.5,0,.96-.33,1.09-.89,.03-.1,.03-.2,.03-.32v-.71Z'/%3E%3Cpath d='M71.51,162.4c0,.25-.18,.46-.47,.46-.26,0-.45-.2-.45-.46s.19-.47,.47-.47,.46,.2,.46,.47Zm-.83,5.25v-4.1h.74v4.1h-.74Z'/%3E%3Cpath d='M72.66,164.66c0-.42,0-.77-.03-1.11h.66l.04,.68h.02c.2-.39,.68-.77,1.35-.77,.57,0,1.45,.34,1.45,1.74v2.45h-.74v-2.36c0-.66-.25-1.21-.95-1.21-.49,0-.87,.35-1,.76-.03,.09-.05,.22-.05,.35v2.46h-.74v-2.99Z'/%3E%3Cpath d='M80.89,163.55c-.02,.3-.03,.63-.03,1.13v2.38c0,.94-.19,1.52-.58,1.87-.4,.37-.97,.49-1.49,.49s-1.03-.12-1.36-.34l.19-.57c.27,.17,.69,.32,1.2,.32,.76,0,1.32-.4,1.32-1.43v-.46h-.02c-.23,.38-.67,.68-1.3,.68-1.02,0-1.74-.86-1.74-2,0-1.39,.91-2.17,1.85-2.17,.71,0,1.1,.37,1.28,.71h.02l.03-.62h.65Zm-.77,1.62c0-.13,0-.24-.04-.34-.14-.43-.5-.79-1.04-.79-.71,0-1.22,.6-1.22,1.55,0,.8,.41,1.47,1.21,1.47,.46,0,.87-.29,1.03-.76,.04-.13,.06-.27,.06-.4v-.74Z'/%3E%3Cpath d='M95.17,115.14c0-19.49-15.8-35.28-35.28-35.28s-35.28,15.8-35.28,35.28,15.8,35.28,35.28,35.28,35.28-15.8,35.28-35.28h0Z' fill='%2348b0f7'/%3E%3Cpath d='M59.88,150.42c9.98,0,19-4.15,25.42-10.81-.39-2.15-.8-4.11-1.18-5.32-1.21-3.88-11.55-7.02-24.3-7.02s-22.98,3.14-24.19,7.02c-.38,1.21-.79,3.16-1.18,5.32,6.42,6.67,15.43,10.82,25.42,10.82Z' fill='%2333333b'/%3E%3Cpath d='M59.89,147.33c2.52,0,5.37-19.77,5.37-19.77l-5.42,3.8-5.34-3.8s2.88,19.77,5.39,19.77h0Z' fill='%23d4d6d8'/%3E%3Cpath d='M54.49,127.56l5.35,3.99,5.43-3.99,.26-1.87-5.69-.75-5.62,.75,.26,1.87Z' fill='%23d4d6d8'/%3E%3Cpath d='M65.41,119.98h-11.06c1.73,5.2,.14,7.58,.14,7.58l3.83,.86h3.13l3.83-.86s-1.59-2.38,.14-7.58h0Z' fill='%23e2a379'/%3E%3Cpath d='M64.72,130.88l.82-5.19,2.54,2.21-3.37,2.98Z' fill='%23f3faff'/%3E%3Cpath d='M55.05,130.88l-.82-5.19-2.54,2.21,3.37,2.98Z' fill='%23f3faff'/%3E%3Cpath d='M68.09,127.9l-2.54-2.21-5.66,2.73s4.84,2.46,4.86,2.43l3.34-2.96Z' fill='%23f3faff'/%3E%3Cpath d='M51.68,127.9l2.54-2.21,5.65,2.73s-4.83,2.46-4.86,2.43l-3.34-2.96h0Z' fill='%23f3faff'/%3E%3Cpath d='M59.88,128.42l-2.24,1.13,2.24,3.64,2.24-3.64-2.24-1.13Z' fill='%2386b4d1'/%3E%3Cpath d='M59.89,147.33c.72,0,1.48-1.64,2.18-3.97l-1.62-12.03h-1.16l-1.6,11.99c.71,2.35,1.47,4.01,2.2,4.01Z' fill='%2386b4d1'/%3E%3Cpath d='M52.56,127.13l-1.78,.92,1.14,7.86,2.32-.52-1.71,2.09,7.35,12.01v-2.15s-4.84-16.45-4.86-16.47l-2.46-3.73Z' fill='%234a4a54'/%3E%3Cpath d='M67.21,127.13l1.78,.92-1.14,7.86-2.32-.52,1.71,2.09-7.35,12.01v-2.15s4.84-16.45,4.86-16.47l2.46-3.73h0Z' fill='%234a4a54'/%3E%3Cpath d='M72.44,104.77c0-13.15-5.62-16.16-12.55-16.16s-12.55,3.01-12.55,16.16c0,4.45,.88,7.93,2.2,10.62,2.9,5.92,7.92,7.98,10.35,7.98s7.45-2.07,10.35-7.98c1.32-2.69,2.2-6.17,2.2-10.62h0Z' fill='%23f4b382'/%3E%3Cpath d='M48.84,113.8c-1.2,.21-2.04,.02-2.72-3.94-.68-3.96,.24-4.48,1.44-4.68l1.28,8.62Z' fill='%23f4b382'/%3E%3Cpath d='M72.44,104.77c0-13.15-5.62-16.16-12.55-16.16s-12.55,3.01-12.55,16.16c0,0,8.9,1.03,16.58-6.08,2.59-2.4,8.52,6.08,8.52,6.08h0Z' fill='%23602f0f'/%3E%3Cpath d='M48.13,99.88c-.6,1.55-.8,3.46-.8,5.33,0,0,1.24-.27,1.24,.37l.39,3.93,.55-.27c-.04-3.27,.69-4.52,.69-4.52l-2.08-4.84Z' fill='%23602f0f'/%3E%3Cpath d='M70.94,113.8c1.2,.21,2.04,.02,2.72-3.94,.68-3.96-.24-4.48-1.44-4.68l-1.28,8.62Z' fill='%23f4b382'/%3E%3Cpath d='M71.65,99.88c.6,1.55,.8,3.46,.8,5.33,0,0-1.24-.27-1.24,.37l-.39,3.93-.55-.27c.04-3.27-.69-4.52-.69-4.52l2.08-4.84Z' fill='%23602f0f'/%3E%3Cpath d='M54.6,113.41s.23-.33,.1-.62c-.38-.83-1.65-.21-1.56,.92,0,0,.09,2.35,3.44,2.46,.87,.03,2.06-.16,3.01-1.21,.65-.72,.48-2.05-.36-2.36-.91-.33-2.07-.09-2.94,1.23-.83,1.26-2.45,.38-2.43-.46,.02-.78,.92-.47,.75,.03Z' fill='%23602f0f'/%3E%3Cpath d='M65.17,113.41s-.23-.33-.1-.62c.38-.83,1.65-.21,1.56,.92,0,0-.09,2.35-3.44,2.46-.87,.03-2.06-.16-3.01-1.21-.65-.72-.48-2.05,.36-2.36,.91-.33,2.07-.09,2.94,1.23,.83,1.26,2.45,.38,2.43-.46-.02-.78-.92-.47-.75,.03Z' fill='%23602f0f'/%3E%3C/svg%3E"
        ),
        width: 120,
        height: 250
    };
}

// /**
//  * @param {Object} values
//  * @param {("web"|"desktop")} platform
//  * @returns {string}
//  */
// export function getCustomCaption(values, platform) {
//     return "NativeOnboarding";
// }
