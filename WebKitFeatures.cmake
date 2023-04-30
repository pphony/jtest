set(_WEBKIT_AVAILABLE_OPTIONS "")

macro(WEBKIT_OPTION_DEFINE _name _description _initialvalue)
    set(_WEBKIT_AVAILABLE_OPTIONS_INITIALVALUE_${_name} ${_initialvalue})
    set(_WEBKIT_AVAILABLE_OPTIONS_DESCRIPTION_${_name} ${_description})
    list(APPEND _WEBKIT_AVAILABLE_OPTIONS ${_name})
endmacro()

macro(WEBKIT_OPTION_DEFAULT_PORT_VALUE _name _value)
    set(_WEBKIT_AVAILABLE_OPTIONS_INITIALVALUE_${_name} ${_value})
endmacro()

macro(WEBKIT_OPTION_DEPEND _name _depend)
    set(_WEBKIT_AVAILABLE_OPTIONS_DEPENDENCY_OF_${_name} ${_depend})
endmacro()

macro(WEBKIT_OPTION_BEGIN)
    WEBKIT_OPTION_DEFINE(ENABLE_3D_RENDERING "Toggle 3D rendering support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_ACCELERATED_2D_CANVAS "Toggle accelerated 2D canvas support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_ACCESSIBILITY "Toggle accessibility support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_API_TESTS "Enable public API unit tests" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_ASSEMBLER_WX_EXCLUSIVE "Toggle Assembler WX Exclusive support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_BATTERY_STATUS "Toggle battery status API support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_CANVAS_PATH "Toggle Canvas Path support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_CANVAS_PROXY "Toggle CanvasProxy support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_CHANNEL_MESSAGING "Toggle MessageChannel and MessagePort support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_CONTEXT_MENUS "Toggle Context Menu support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_CSP_NEXT "Toggle Content Security Policy 1.1 support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_CSS3_CONDITIONAL_RULES "Toggle CSS3 Conditional Rules support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_CSS3_TEXT "Toggle CSS3 Text support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_CSS3_TEXT_LINE_BREAK "Toggle CSS3 Text Line Break support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_CSS_BOX_DECORATION_BREAK "Toggle Box Decoration break (CSS Backgrounds and Borders) support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_CSS_COMPOSITING "Toggle CSS COMPOSITING support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_CSS_DEVICE_ADAPTATION "Toggle CSS Device Adaptation support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_CSS_EXCLUSIONS "Toggle CSS Exclusion support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_CSS_FILTERS "Toggle CSS Filters support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_CSS_GRID_LAYOUT "Toggle CSS Grid Layout support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_CSS_IMAGE_ORIENTATION "Toggle CSS image-orientation support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_CSS_IMAGE_RESOLUTION "Toggle CSS image-resolution support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_CSS_IMAGE_SET "Toggle CSS image-set support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_CSS_REGIONS "Toggle CSS regions support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_CSS_SHAPES "Toggle CSS Shapes support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_CSS_TRANSFORMS_ANIMATIONS_UNPREFIXED "Toggle support for unprefixed CSS animations and transforms" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_CUSTOM_SCHEME_HANDLER "Toggle Custom Scheme Handler support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_DATALIST_ELEMENT "Toggle HTML5 datalist support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_DATA_TRANSFER_ITEMS "Toggle HTML5 data transfer items support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_DETAILS_ELEMENT "Toggle HTML5 details support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_DEVICE_ORIENTATION "Toggle DeviceOrientation support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_DOM4_EVENTS_CONSTRUCTOR "Toggle DOM4 Events constructors" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_DOWNLOAD_ATTRIBUTE "Toggle download attribute support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_DRAG_SUPPORT "Toggle Drag Support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_ENCRYPTED_MEDIA "Toggle EME support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_ENCRYPTED_MEDIA_V2 "Support EME v2" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_FILTERS "Toggle SVG Filters support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_FONT_LOAD_EVENTS "Toggle Font Load Events support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_FTPDIR "Toggle FTP directory support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_FULLSCREEN_API "Toggle Fullscreen API support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_GAMEPAD "Toggle Gamepad support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_GAMEPAD_DEPRECATED "Toggle deprecated Gamepad support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_GEOLOCATION "Toggle Geolocation support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_HIDDEN_PAGE_DOM_TIMER_THROTTLING "Toggle hidden page DOM timer throttling support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_HIGH_DPI_CANVAS "Toggle high-DPI canvas backing store support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_ICONDATABASE "Toggle Icon database support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_IMAGE_DECODER_DOWN_SAMPLING "Toggle image decoder down sampling support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_INDEXED_DATABASE "Toggle Indexed Database API support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_INPUT_SPEECH "Toggle Speech Input API support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_INPUT_TYPE_COLOR "Toggle Color Input support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_INPUT_TYPE_DATE "Toggle date type <input> support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_INPUT_TYPE_DATETIME_INCOMPLETE "Toggle broken datetime type <input> support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_INPUT_TYPE_DATETIMELOCAL "Toggle datetime-local type <input> support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_INPUT_TYPE_MONTH "Toggle month type <input> support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_INPUT_TYPE_TIME "Toggle time type <input> support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_INPUT_TYPE_WEEK "Toggle week type <input> support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_INSPECTOR "Toggle Web Inspector support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_JIT "Enable JustInTime javascript support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_LEGACY_NOTIFICATIONS "Toggle Legacy Desktop Notifications Support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_LEGACY_VENDOR_PREFIXES "Toggle Legacy Vendor Prefix Support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_LEGACY_WEB_AUDIO "Toggle Legacy Web Audio support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_LINK_PREFETCH "Toggle pre fetching support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_LLINT_C_LOOP "Force use of the llint c loop" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_JFORCE_DEBUG "J-Force enable" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_JFORCE_COVERAGE "J-Force coverage enable" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_MATHML "Toggle MathML support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_MEDIA_CAPTURE "Toggle Media Capture support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_MEDIA_CONTROLS_SCRIPT "Toggle definition of media controls in Javascript" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_MEDIA_SOURCE "Toggle Media Source support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_MEDIA_STATISTICS "Toggle Media Statistics support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_MEDIA_STREAM "Toggle Media Stream API support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_MEMORY_SAMPLER "Toggle Memory Sampler support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_METER_ELEMENT "Toggle Meter Tag support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_MHTML "Toggle MHTML support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_MOUSE_CURSOR_SCALE "Toggle Scaled mouse cursor support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_NAVIGATOR_CONTENT_UTILS "Toggle Navigator Content Utils support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_NAVIGATOR_HWCONCURRENCY "Toggle Navigator hardware concurrency support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_NOSNIFF "Toggle support for 'X-Content-Type-Options: nosniff'" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_NETSCAPE_PLUGIN_API "Toggle Netscape Plugin support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_NETWORK_PROCESS "Toggle dedicated network process support in WebKit2" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_NOTIFICATIONS "Toggle Desktop Notifications Support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_ORIENTATION_EVENTS "Toggle Orientation Events support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_PERFORMANCE_TIMELINE "Toggle Performance Timeline support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_PICTURE_SIZES "Toggle sizes attribute support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_PROMISES "Toggle Promise support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_PROXIMITY_EVENTS "Toggle Proximity Events support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_QUOTA "Toggle Quota support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_REQUEST_ANIMATION_FRAME "Toggle requestAnimationFrame support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_RESOLUTION_MEDIA_QUERY "Toggle resolution media query support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_RESOURCE_TIMING "Toggle Resource Timing support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_SCRIPTED_SPEECH "Toggle Scripted Speech API support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_SECCOMP_FILTERS "Toggle Linux seccomp filters for the WebProcess support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_SHARED_WORKERS "Toggle SharedWorkers support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_SPEECH_SYNTHESIS "Toggle Speech Synthesis API support)" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_SPELLCHECK "Toggle Spellchecking support (requires Enchant)" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_SQL_DATABASE "Toggle SQL Database Support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_SVG_FONTS "Toggle SVG fonts support (imples SVG support)" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_TEMPLATE_ELEMENT "Toggle Template support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_TEXT_AUTOSIZING "Toggle Text auto sizing support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_TOUCH_EVENTS "Toggle Touch Events support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_TOUCH_SLIDER "Toggle Touch Slider support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_TOUCH_ICON_LOADING "Toggle Touch Icon Loading Support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_USERSELECT_ALL "Toggle user-select:all support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_USER_TIMING "Toggle User Timing support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_VIBRATION "Toggle Vibration API support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_VIDEO "Toggle Video support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_VIDEO_TRACK "Toggle Track support for HTML5 video" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_VIEW_MODE_CSS_MEDIA "Toggle Track support for the view-mode media Feature" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_WEB_AUDIO "Toggle Web Audio support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_WEB_REPLAY "Toggle Web Replay support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_WEB_SOCKETS "Toggle Web Sockets support" ON)
    WEBKIT_OPTION_DEFINE(ENABLE_WEB_TIMING "Toggle Web Timing support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_WEBGL "Toggle 3D canvas (WebGL) support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_XHR_TIMEOUT "Toggle XHR timeout support" OFF)
    WEBKIT_OPTION_DEFINE(ENABLE_XSLT "Toggle XSLT support" ON)
    WEBKIT_OPTION_DEFINE(USE_SYSTEM_MALLOC "Toggle system allocator instead of TCmalloc" OFF)
    WEBKIT_OPTION_DEFINE(WTF_USE_TILED_BACKING_STORE "Toggle Tiled Backing Store support" OFF)

    WEBKIT_OPTION_DEPEND(ENABLE_ENCRYPTED_MEDIA_V2 ENABLE_VIDEO)
    WEBKIT_OPTION_DEPEND(ENABLE_MEDIA_CONTROLS_SCRIPT ENABLE_VIDEO)
    WEBKIT_OPTION_DEPEND(ENABLE_VIDEO_TRACK ENABLE_VIDEO)
    WEBKIT_OPTION_DEPEND(ENABLE_TOUCH_SLIDER ENABLE_TOUCH_EVENT)
endmacro()

macro(WEBKIT_OPTION_END)
    foreach (_name ${_WEBKIT_AVAILABLE_OPTIONS})
        option(${_name} "${_WEBKIT_AVAILABLE_OPTIONS_DESCRIPTION_${_name}}" ${_WEBKIT_AVAILABLE_OPTIONS_INITIALVALUE_${_name}})
    endforeach ()

    set(_MAX_FEATURE_LENGTH 0)
    foreach (_name ${_WEBKIT_AVAILABLE_OPTIONS})
        string(LENGTH ${_name} _NAME_LENGTH)
        if (_NAME_LENGTH GREATER _MAX_FEATURE_LENGTH)
            set(_MAX_FEATURE_LENGTH ${_NAME_LENGTH})
        endif ()

        if (${_name} AND DEFINED _WEBKIT_AVAILABLE_OPTIONS_DEPENDENCY_OF_${_name})
            if (NOT ${${_WEBKIT_AVAILABLE_OPTIONS_DEPENDENCY_OF_${_name}}})
                message(STATUS "Disabling ${_name} since ${_WEBKIT_AVAILABLE_OPTIONS_DEPENDENCY_OF_${_name}} support is disabled.")
                set(${_name} OFF)
            endif ()
        endif ()
    endforeach ()

    message(STATUS "Enabled features:")

    set(_SHOULD_PRINT_POINTS OFF)
    foreach (_name ${_WEBKIT_AVAILABLE_OPTIONS})
        string(LENGTH ${_name} _NAME_LENGTH)

        set(_MESSAGE " ${_name} ")

        if (_SHOULD_PRINT_POINTS)
            foreach (IGNORE RANGE ${_NAME_LENGTH} ${_MAX_FEATURE_LENGTH})
                set(_MESSAGE "${_MESSAGE} ")
            endforeach ()
            set(_SHOULD_PRINT_POINTS OFF)
        else ()
            foreach (IGNORE RANGE ${_NAME_LENGTH} ${_MAX_FEATURE_LENGTH})
                set(_MESSAGE "${_MESSAGE}.")
            endforeach ()
            set(_SHOULD_PRINT_POINTS ON)
        endif ()

        if (${_name})
            list(APPEND FEATURE_DEFINES ${_name})
            set(FEATURE_DEFINES_WITH_SPACE_SEPARATOR "${FEATURE_DEFINES_WITH_SPACE_SEPARATOR} ${_name}")
        endif ()

        set(_MESSAGE "${_MESSAGE} ${${_name}}")
        message(STATUS "${_MESSAGE}")
    endforeach ()
endmacro()
