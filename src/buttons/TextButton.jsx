import { Text, TouchableOpacity } from "react-native";
import adjustFont from "../util/adjustfont";
import { createElement } from "react";

const TextButton = ({ fontSize, marginLeft, marginRight, textColor, title, ...props }) => (
    <TouchableOpacity
        style={{ flex: 0 }}
        hitSlop={{ top: 15, bottom: 15, left: 15, right: 15 }}
        containerViewStyle={{ margin: 10 }}
        {...props}
    >
        <Text
            style={{
                color: textColor,
                fontSize: adjustFont(fontSize),
                marginLeft: marginLeft,
                marginRight: marginRight
            }}
        >
            {title}
        </Text>
    </TouchableOpacity>
);

export default TextButton;
